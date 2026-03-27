enum BoundType {
    BOUND_EXACT = 0,
    BOUND_LOWER = 1,
    BOUND_UPPER = 2,
};

struct TtEntry {
    std::uint64_t key = 0;
    double score = 0.0;
    int depth = -1;
    int flag = BOUND_EXACT;
    Move best_move{};
    bool has_move = false;
};

std::uint64_t splitmix64(std::uint64_t x) {
    x += 0x9e3779b97f4a7c15ULL;
    x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
    x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
    return x ^ (x >> 31);
}

bool same_mv(const Move &lhs, const Move &rhs) {
    return lhs.from == rhs.from &&
           lhs.to == rhs.to &&
           lhs.promotion == rhs.promotion &&
           lhs.is_en_passant == rhs.is_en_passant &&
           lhs.is_castling == rhs.is_castling;
}

std::array<std::array<std::uint64_t, 64>, 12> g_piece_keys{};
std::array<std::uint64_t, 16> g_castle_keys{};
std::array<std::uint64_t, 9> g_ep_keys{};
std::uint64_t g_side_key = 0;
bool g_hash_ready = false;

int piece_key_idx(int piece) {
    int type = piece_type(piece) - 1;
    int color_offset = is_white_piece(piece) ? 0 : 6;
    return color_offset + type;
}

int ep_key_idx(int ep_square) {
    return ep_square == -1 ? 8 : file_of(ep_square);
}

void init_hash_keys_once() {
    if (g_hash_ready) {
        return;
    }

    // Not crypto, just fast and stable enough for TT keys.
    std::uint64_t seed = 0x9e3779b97f4a7c15ULL;
    for (auto &piece_table : g_piece_keys) {
        for (auto &slot : piece_table) {
            seed = splitmix64(seed);
            slot = seed;
        }
    }
    for (auto &slot : g_castle_keys) {
        seed = splitmix64(seed);
        slot = seed;
    }
    for (auto &slot : g_ep_keys) {
        seed = splitmix64(seed);
        slot = seed;
    }
    seed = splitmix64(seed);
    g_side_key = seed;
    g_hash_ready = true;
}

int ep_square_after(const Board &b, const Move &move, int moved_piece) {
    if (piece_type(moved_piece) == PAWN && std::abs(rank_of(move.to) - rank_of(move.from)) == 2) {
        return b.white_to_move ? (move.from + 8) : (move.from - 8);
    }
    return -1;
}

int castle_rights_after(const Board &b, const Move &move, int moved_piece, int captured_piece) {
    int rights = b.castling_rights;
    auto clear_if_on = [&](int square) {
        if (square == square_from_string("a1")) {
            rights &= ~WHITE_QUEENSIDE;
        } else if (square == square_from_string("h1")) {
            rights &= ~WHITE_KINGSIDE;
        } else if (square == square_from_string("a8")) {
            rights &= ~BLACK_QUEENSIDE;
        } else if (square == square_from_string("h8")) {
            rights &= ~BLACK_KINGSIDE;
        }
    };

    if (piece_type(moved_piece) == KING) {
        if (is_white_piece(moved_piece)) {
            rights &= ~(WHITE_KINGSIDE | WHITE_QUEENSIDE);
        } else {
            rights &= ~(BLACK_KINGSIDE | BLACK_QUEENSIDE);
        }
    }
    if (piece_type(moved_piece) == ROOK) {
        clear_if_on(move.from);
    }
    if (captured_piece != EMPTY) {
        clear_if_on(move.to);
    }
    return rights;
}

std::uint64_t modern_hash_position(const Board &board) {
    init_hash_keys_once();

    std::uint64_t key = 0;
    for (int sq = 0; sq < 64; ++sq) {
        int piece = board.squares[sq];
        if (piece == EMPTY) {
            continue;
        }
        key ^= g_piece_keys[piece_key_idx(piece)][sq];
    }
    key ^= g_castle_keys[board.castling_rights & 15];
    key ^= g_ep_keys[ep_key_idx(board.ep_square)];
    if (!board.white_to_move) {
        key ^= g_side_key;
    }
    return key;
}

std::uint64_t modern_hash_after_move(const Board &board, const Move &move) {
    init_hash_keys_once();

    std::uint64_t key = board.hash_key;
    int moved_piece = board.squares[move.from];
    int captured_piece = EMPTY;
    int captured_square = move.to;
    if (move.is_en_passant) {
        captured_square = board.white_to_move ? (move.to - 8) : (move.to + 8);
        captured_piece = board.squares[captured_square];
    } else {
        captured_piece = board.squares[move.to];
    }

    key ^= g_side_key;
    key ^= g_castle_keys[board.castling_rights & 15];
    key ^= g_ep_keys[ep_key_idx(board.ep_square)];

    key ^= g_piece_keys[piece_key_idx(moved_piece)][move.from];
    if (captured_piece != EMPTY) {
        key ^= g_piece_keys[piece_key_idx(captured_piece)][captured_square];
    }

    if (move.is_castling) {
        int rook_piece = board.white_to_move ? ROOK : -ROOK;
        int rook_from = -1;
        int rook_to = -1;
        if (move.to == square_from_string("g1")) {
            rook_from = square_from_string("h1");
            rook_to = square_from_string("f1");
        } else if (move.to == square_from_string("c1")) {
            rook_from = square_from_string("a1");
            rook_to = square_from_string("d1");
        } else if (move.to == square_from_string("g8")) {
            rook_from = square_from_string("h8");
            rook_to = square_from_string("f8");
        } else if (move.to == square_from_string("c8")) {
            rook_from = square_from_string("a8");
            rook_to = square_from_string("d8");
        }
        if (rook_from != -1) {
            key ^= g_piece_keys[piece_key_idx(rook_piece)][rook_from];
            key ^= g_piece_keys[piece_key_idx(rook_piece)][rook_to];
        }
    }

    int placed_piece = moved_piece;
    if (move.promotion != EMPTY) {
        placed_piece = make_piece(board.white_to_move, move.promotion);
    }
    key ^= g_piece_keys[piece_key_idx(placed_piece)][move.to];

    key ^= g_castle_keys[castle_rights_after(board, move, moved_piece, captured_piece) & 15];
    key ^= g_ep_keys[ep_key_idx(ep_square_after(board, move, moved_piece))];
    return key;
}

class ModernSearchState {
  public:
    static constexpr int kMaxPly = 128;

    ModernSearchState() {
        init_zobrist();
        resize_tt(16);
        clear_ordering();
    }

    void resize_tt(int hash_mb) {
        hash_mb = std::max(1, hash_mb);
        std::size_t bytes = static_cast<std::size_t>(hash_mb) * 1024ULL * 1024ULL;
        std::size_t count = bytes / sizeof(TtEntry);
        if (count < 1) {
            count = 1;
        }
        tt.assign(count, TtEntry{});
    }

    void clear_tt() {
        for (auto &entry : tt) {
            entry = TtEntry{};
        }
    }

    void clear_ordering() {
        for (auto &slot : killer_valid) {
            slot = {false, false};
        }
        for (auto &side : history) {
            for (auto &from : side) {
                from.fill(0);
            }
        }
    }

    std::uint64_t position_key(const Board &b) const {
        std::uint64_t key = 0;
        for (int sq = 0; sq < 64; ++sq) {
            int piece = b.squares[sq];
            if (piece == EMPTY) {
                continue;
            }
            key ^= zobrist_piece[piece_index(piece)][sq];
        }

        key ^= zobrist_castle[b.castling_rights & 15];
        key ^= zobrist_ep[ep_index(b.ep_square)];
        if (!b.white_to_move) {
            key ^= zobrist_side;
        }
        return key;
    }

    std::uint64_t next_key(const Board &b, const Move &move, std::uint64_t key_before) const {
        std::uint64_t key = key_before;
        int moved_piece = b.squares[move.from];
        int captured_piece = EMPTY;
        int captured_square = move.to;
        if (move.is_en_passant) {
            captured_square = b.white_to_move ? (move.to - 8) : (move.to + 8);
            captured_piece = b.squares[captured_square];
        } else {
            captured_piece = b.squares[move.to];
        }

        key ^= zobrist_side;
        key ^= zobrist_castle[b.castling_rights & 15];
        key ^= zobrist_ep[ep_index(b.ep_square)];

        key ^= zobrist_piece[piece_index(moved_piece)][move.from];
        if (captured_piece != EMPTY) {
            key ^= zobrist_piece[piece_index(captured_piece)][captured_square];
        }

        if (move.is_castling) {
            int rook_piece = b.white_to_move ? ROOK : -ROOK;
            int rook_from = -1;
            int rook_to = -1;
            if (move.to == square_from_string("g1")) {
                rook_from = square_from_string("h1");
                rook_to = square_from_string("f1");
            } else if (move.to == square_from_string("c1")) {
                rook_from = square_from_string("a1");
                rook_to = square_from_string("d1");
            } else if (move.to == square_from_string("g8")) {
                rook_from = square_from_string("h8");
                rook_to = square_from_string("f8");
            } else if (move.to == square_from_string("c8")) {
                rook_from = square_from_string("a8");
                rook_to = square_from_string("d8");
            }
            if (rook_from != -1) {
                key ^= zobrist_piece[piece_index(rook_piece)][rook_from];
                key ^= zobrist_piece[piece_index(rook_piece)][rook_to];
            }
        }

        int placed_piece = moved_piece;
        if (move.promotion != EMPTY) {
            placed_piece = make_piece(b.white_to_move, move.promotion);
        }
        key ^= zobrist_piece[piece_index(placed_piece)][move.to];

        key ^= zobrist_castle[updated_castling_rights(b, move, moved_piece, captured_piece) & 15];
        key ^= zobrist_ep[ep_index(next_ep_square(b, move, moved_piece))];
        return key;
    }

    const TtEntry *probe(std::uint64_t key) const {
        if (tt.empty()) {
            return nullptr;
        }
        const auto &entry = tt[key % tt.size()];
        if (entry.key != key) {
            return nullptr;
        }
        return &entry;
    }

    void store(std::uint64_t key, int depth, double score, int flag, const Move *best_move) {
        if (tt.empty()) {
            return;
        }
        auto &entry = tt[key % tt.size()];
        if (entry.depth > depth && entry.key == key) {
            return;
        }
        entry.key = key;
        entry.depth = depth;
        entry.score = score;
        entry.flag = flag;
        entry.has_move = best_move != nullptr;
        entry.best_move = best_move ? *best_move : Move{};
    }

    void promote_tt_move(std::vector<Move> &moves, const Move &tt_move) const {
        auto it = std::find_if(moves.begin(), moves.end(), [&](const Move &mv) {
            return same_mv(mv, tt_move);
        });
        if (it != moves.end() && it != moves.begin()) {
            std::rotate(moves.begin(), it, it + 1);
        }
    }

    int killer_bonus(int ply, const Move &move) const {
        if (ply < 0 || ply >= kMaxPly) {
            return 0;
        }
        if (killer_valid[ply][0] && same_mv(killer_moves[ply][0], move)) {
            return 9000;
        }
        if (killer_valid[ply][1] && same_mv(killer_moves[ply][1], move)) {
            return 7000;
        }
        return 0;
    }

    int history_bonus(bool white, const Move &move) const {
        return history[white ? 0 : 1][move.from][move.to];
    }

    void note_cutoff(bool white, int ply, const Move &move, bool is_capture, int depth) {
        if (is_capture) {
            return;
        }

        if (ply >= 0 && ply < kMaxPly) {
            if (!killer_valid[ply][0] || !same_mv(killer_moves[ply][0], move)) {
                killer_moves[ply][1] = killer_moves[ply][0];
                killer_valid[ply][1] = killer_valid[ply][0];
                killer_moves[ply][0] = move;
                killer_valid[ply][0] = true;
            }
        }

        int &hist = history[white ? 0 : 1][move.from][move.to];
        hist = std::min(hist + depth * depth * 32, 2000000);
    }

  private:
    std::array<std::array<std::uint64_t, 64>, 12> zobrist_piece{};
    std::array<std::uint64_t, 16> zobrist_castle{};
    std::array<std::uint64_t, 9> zobrist_ep{};
    std::uint64_t zobrist_side = 0;
    std::vector<TtEntry> tt;
    std::array<std::array<Move, 2>, kMaxPly> killer_moves{};
    std::array<std::array<bool, 2>, kMaxPly> killer_valid{};
    std::array<std::array<std::array<int, 64>, 64>, 2> history{};

    void init_zobrist() {
        std::uint64_t seed = 0x9e3779b97f4a7c15ULL;
        for (auto &piece_table : zobrist_piece) {
            for (auto &slot : piece_table) {
                seed = splitmix64(seed);
                slot = seed;
            }
        }
        for (auto &slot : zobrist_castle) {
            seed = splitmix64(seed);
            slot = seed;
        }
        for (auto &slot : zobrist_ep) {
            seed = splitmix64(seed);
            slot = seed;
        }
        seed = splitmix64(seed);
        zobrist_side = seed;
    }

    int piece_index(int piece) const {
        int type = piece_type(piece) - 1;
        int color_offset = is_white_piece(piece) ? 0 : 6;
        return color_offset + type;
    }

    int ep_index(int ep_square) const {
        return ep_square == -1 ? 8 : file_of(ep_square);
    }

    int next_ep_square(const Board &b, const Move &move, int moved_piece) const {
        if (piece_type(moved_piece) == PAWN && std::abs(rank_of(move.to) - rank_of(move.from)) == 2) {
            return b.white_to_move ? (move.from + 8) : (move.from - 8);
        }
        return -1;
    }

    int updated_castling_rights(const Board &b, const Move &move, int moved_piece, int captured_piece) const {
        int rights = b.castling_rights;
        auto clear_if_on = [&](int square) {
            if (square == square_from_string("a1")) {
                rights &= ~WHITE_QUEENSIDE;
            } else if (square == square_from_string("h1")) {
                rights &= ~WHITE_KINGSIDE;
            } else if (square == square_from_string("a8")) {
                rights &= ~BLACK_QUEENSIDE;
            } else if (square == square_from_string("h8")) {
                rights &= ~BLACK_KINGSIDE;
            }
        };

        if (piece_type(moved_piece) == KING) {
            if (is_white_piece(moved_piece)) {
                rights &= ~(WHITE_KINGSIDE | WHITE_QUEENSIDE);
            } else {
                rights &= ~(BLACK_KINGSIDE | BLACK_QUEENSIDE);
            }
        }
        if (piece_type(moved_piece) == ROOK) {
            clear_if_on(move.from);
        }
        if (captured_piece != EMPTY) {
            clear_if_on(move.to);
        }
        return rights;
    }
};
