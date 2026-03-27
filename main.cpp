#include <algorithm>
#include <array>
#include <bit>
#include <cmath>
#include <cctype>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <optional>
#include <sstream>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

namespace {

constexpr double kMateScore = 10000.0;
constexpr double kInf = 1e18;
constexpr int kMaxDepth = 4;
constexpr std::array<double, 7> kPieceValues = {0.0, 1.0, 3.0, 3.5, 5.0, 10.0, 0.0};

enum PieceType {
    EMPTY = 0,
    PAWN = 1,
    KNIGHT = 2,
    BISHOP = 3,
    ROOK = 4,
    QUEEN = 5,
    KING = 6,
};

enum CastlingRights {
    WHITE_KINGSIDE = 1 << 0,
    WHITE_QUEENSIDE = 1 << 1,
    BLACK_KINGSIDE = 1 << 2,
    BLACK_QUEENSIDE = 1 << 3,
};

struct Move {
    int from = -1;
    int to = -1;
    int promotion = EMPTY;
    bool is_en_passant = false;
    bool is_castling = false;
};

struct UndoState {
    int captured_piece = EMPTY;
    int moved_piece = EMPTY;
    int castling_rights = 0;
    int ep_square = -1;
    int halfmove_clock = 0;
    int fullmove_number = 1;
    bool white_to_move = true;
    std::uint64_t hash_key = 0;
    bool position_play_valid = false;
    double position_play_cache = 0.0;
};

struct SearchResult {
    double score = 0.0;
    std::vector<Move> pv;
};

int piece_color(int piece) {
    if (piece > 0) {
        return 1;
    }
    if (piece < 0) {
        return -1;
    }
    return 0;
}

int piece_type(int piece) {
    return std::abs(piece);
}

bool is_white_piece(int piece) {
    return piece > 0;
}

int make_piece(bool white, int type) {
    return white ? type : -type;
}

int file_of(int square) {
    return square % 8;
}

int rank_of(int square) {
    return square / 8;
}

bool on_board(int square) {
    return square >= 0 && square < 64;
}

std::string square_to_string(int square) {
    std::string text = "a1";
    text[0] = static_cast<char>('a' + file_of(square));
    text[1] = static_cast<char>('1' + rank_of(square));
    return text;
}

int square_from_string(const std::string &text) {
    if (text.size() != 2) {
        return -1;
    }
    int file = text[0] - 'a';
    int rank = text[1] - '1';
    if (file < 0 || file >= 8 || rank < 0 || rank >= 8) {
        return -1;
    }
    return rank * 8 + file;
}

char promotion_char(int type) {
    switch (type) {
        case KNIGHT:
            return 'n';
        case BISHOP:
            return 'b';
        case ROOK:
            return 'r';
        case QUEEN:
            return 'q';
        default:
            return '\0';
    }
}

std::string move_to_uci(const Move &move) {
    std::string text = square_to_string(move.from) + square_to_string(move.to);
    if (move.promotion != EMPTY) {
        text.push_back(promotion_char(move.promotion));
    }
    return text;
}

using Bitboard = std::uint64_t;

constexpr Bitboard bit_for(int square) {
    return 1ULL << square;
}

int lsb_square(Bitboard bb) {
    return static_cast<int>(std::countr_zero(bb));
}

int pop_lsb(Bitboard &bb) {
    int square = lsb_square(bb);
    bb &= bb - 1;
    return square;
}

std::array<Bitboard, 64> g_knight_attacks{};
std::array<Bitboard, 64> g_king_attacks{};
std::array<std::array<Bitboard, 64>, 2> g_pawn_attacks{};
bool g_attack_tables_ready = false;

Bitboard rook_attacks(int square, Bitboard occ) {
    Bitboard attacks = 0;
    int file = file_of(square);
    int rank = rank_of(square);

    for (int nf = file + 1; nf < 8; ++nf) {
        int to = rank * 8 + nf;
        attacks |= bit_for(to);
        if (occ & bit_for(to)) {
            break;
        }
    }
    for (int nf = file - 1; nf >= 0; --nf) {
        int to = rank * 8 + nf;
        attacks |= bit_for(to);
        if (occ & bit_for(to)) {
            break;
        }
    }
    for (int nr = rank + 1; nr < 8; ++nr) {
        int to = nr * 8 + file;
        attacks |= bit_for(to);
        if (occ & bit_for(to)) {
            break;
        }
    }
    for (int nr = rank - 1; nr >= 0; --nr) {
        int to = nr * 8 + file;
        attacks |= bit_for(to);
        if (occ & bit_for(to)) {
            break;
        }
    }

    return attacks;
}

Bitboard bishop_attacks(int square, Bitboard occ) {
    Bitboard attacks = 0;
    int file = file_of(square);
    int rank = rank_of(square);

    for (int nf = file + 1, nr = rank + 1; nf < 8 && nr < 8; ++nf, ++nr) {
        int to = nr * 8 + nf;
        attacks |= bit_for(to);
        if (occ & bit_for(to)) {
            break;
        }
    }
    for (int nf = file + 1, nr = rank - 1; nf < 8 && nr >= 0; ++nf, --nr) {
        int to = nr * 8 + nf;
        attacks |= bit_for(to);
        if (occ & bit_for(to)) {
            break;
        }
    }
    for (int nf = file - 1, nr = rank + 1; nf >= 0 && nr < 8; --nf, ++nr) {
        int to = nr * 8 + nf;
        attacks |= bit_for(to);
        if (occ & bit_for(to)) {
            break;
        }
    }
    for (int nf = file - 1, nr = rank - 1; nf >= 0 && nr >= 0; --nf, --nr) {
        int to = nr * 8 + nf;
        attacks |= bit_for(to);
        if (occ & bit_for(to)) {
            break;
        }
    }

    return attacks;
}

void init_attack_tables_once() {
    if (g_attack_tables_ready) {
        return;
    }

    for (int square = 0; square < 64; ++square) {
        int file = file_of(square);
        int rank = rank_of(square);

        static const int knight_offsets[8][2] = {
            {1, 2}, {2, 1}, {2, -1}, {1, -2},
            {-1, -2}, {-2, -1}, {-2, 1}, {-1, 2},
        };
        static const int king_offsets[8][2] = {
            {1, 0}, {1, 1}, {0, 1}, {-1, 1},
            {-1, 0}, {-1, -1}, {0, -1}, {1, -1},
        };

        Bitboard knight_mask = 0;
        for (const auto &offset : knight_offsets) {
            int nf = file + offset[0];
            int nr = rank + offset[1];
            if (nf >= 0 && nf < 8 && nr >= 0 && nr < 8) {
                knight_mask |= bit_for(nr * 8 + nf);
            }
        }
        g_knight_attacks[square] = knight_mask;

        Bitboard king_mask = 0;
        for (const auto &offset : king_offsets) {
            int nf = file + offset[0];
            int nr = rank + offset[1];
            if (nf >= 0 && nf < 8 && nr >= 0 && nr < 8) {
                king_mask |= bit_for(nr * 8 + nf);
            }
        }
        g_king_attacks[square] = king_mask;

        Bitboard white_pawns = 0;
        Bitboard black_pawns = 0;
        for (int df : {-1, 1}) {
            int wf = file + df;
            int wr = rank + 1;
            if (wf >= 0 && wf < 8 && wr >= 0 && wr < 8) {
                white_pawns |= bit_for(wr * 8 + wf);
            }
            int bf = file + df;
            int br = rank - 1;
            if (bf >= 0 && bf < 8 && br >= 0 && br < 8) {
                black_pawns |= bit_for(br * 8 + bf);
            }
        }
        g_pawn_attacks[0][square] = white_pawns;
        g_pawn_attacks[1][square] = black_pawns;

    }

    g_attack_tables_ready = true;
}

class Board;

std::uint64_t modern_hash_position(const Board &board);
std::uint64_t modern_hash_after_move(const Board &board, const Move &move);

class Board {
  public:
    static constexpr int kPieceListCap = 32;

    std::array<int, 64> squares{};
    std::array<int, 64> piece_slot{};
    std::array<std::array<std::array<int, kPieceListCap>, 7>, 2> piece_list{};
    std::array<std::array<int, 7>, 2> piece_count{};
    std::array<std::array<Bitboard, 7>, 2> piece_bb{};
    std::array<Bitboard, 2> occ{};
    Bitboard occ_all = 0;
    std::array<int, 2> king_sq{{-1, -1}};
    bool white_to_move = true;
    int castling_rights = WHITE_KINGSIDE | WHITE_QUEENSIDE | BLACK_KINGSIDE | BLACK_QUEENSIDE;
    int ep_square = -1;
    int halfmove_clock = 0;
    int fullmove_number = 1;
    std::uint64_t hash_key = 0;
    bool position_play_valid = false;
    double position_play_cache = 0.0;

    Board() {
        set_startpos();
    }

    void set_startpos() {
        set_fen("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");
    }

    void set_fen(const std::string &fen) {
        init_attack_tables_once();
        squares.fill(EMPTY);
        piece_slot.fill(-1);
        clear_piece_lists();
        std::istringstream stream(fen);
        std::string board_part;
        std::string stm_part;
        std::string castling_part;
        std::string ep_part;
        stream >> board_part >> stm_part >> castling_part >> ep_part >> halfmove_clock >> fullmove_number;

        int rank = 7;
        int file = 0;
        for (char c : board_part) {
            if (c == '/') {
                --rank;
                file = 0;
                continue;
            }
            if (std::isdigit(static_cast<unsigned char>(c))) {
                file += c - '0';
                continue;
            }
            int type = EMPTY;
            switch (std::tolower(static_cast<unsigned char>(c))) {
                case 'p':
                    type = PAWN;
                    break;
                case 'n':
                    type = KNIGHT;
                    break;
                case 'b':
                    type = BISHOP;
                    break;
                case 'r':
                    type = ROOK;
                    break;
                case 'q':
                    type = QUEEN;
                    break;
                case 'k':
                    type = KING;
                    break;
            }
            bool white = std::isupper(static_cast<unsigned char>(c));
            int sq = rank * 8 + file;
            squares[sq] = make_piece(white, type);
            add_piece_state(sq, squares[sq]);
            ++file;
        }

        white_to_move = (stm_part == "w");
        castling_rights = 0;
        if (castling_part.find('K') != std::string::npos) {
            castling_rights |= WHITE_KINGSIDE;
        }
        if (castling_part.find('Q') != std::string::npos) {
            castling_rights |= WHITE_QUEENSIDE;
        }
        if (castling_part.find('k') != std::string::npos) {
            castling_rights |= BLACK_KINGSIDE;
        }
        if (castling_part.find('q') != std::string::npos) {
            castling_rights |= BLACK_QUEENSIDE;
        }
        ep_square = (ep_part == "-") ? -1 : square_from_string(ep_part);
        hash_key = modern_hash_position(*this);
        position_play_valid = false;
    }

    std::string epd() const {
        std::ostringstream out;
        for (int rank = 7; rank >= 0; --rank) {
            int empties = 0;
            for (int file = 0; file < 8; ++file) {
                int piece = squares[rank * 8 + file];
                if (piece == EMPTY) {
                    ++empties;
                    continue;
                }
                if (empties) {
                    out << empties;
                    empties = 0;
                }
                char c = ' ';
                switch (piece_type(piece)) {
                    case PAWN:
                        c = 'p';
                        break;
                    case KNIGHT:
                        c = 'n';
                        break;
                    case BISHOP:
                        c = 'b';
                        break;
                    case ROOK:
                        c = 'r';
                        break;
                    case QUEEN:
                        c = 'q';
                        break;
                    case KING:
                        c = 'k';
                        break;
                    default:
                        break;
                }
                if (is_white_piece(piece)) {
                    c = static_cast<char>(std::toupper(static_cast<unsigned char>(c)));
                }
                out << c;
            }
            if (empties) {
                out << empties;
            }
            if (rank > 0) {
                out << '/';
            }
        }
        out << (white_to_move ? " w " : " b ");
        std::string castling = "-";
        if (castling_rights) {
            castling.clear();
            if (castling_rights & WHITE_KINGSIDE) {
                castling.push_back('K');
            }
            if (castling_rights & WHITE_QUEENSIDE) {
                castling.push_back('Q');
            }
            if (castling_rights & BLACK_KINGSIDE) {
                castling.push_back('k');
            }
            if (castling_rights & BLACK_QUEENSIDE) {
                castling.push_back('q');
            }
        }
        out << castling << ' ';
        out << (ep_square == -1 ? "-" : square_to_string(ep_square));
        return out.str();
    }

    int king_square(bool white) const {
        return king_sq[color_index(white)];
    }

    bool is_square_attacked(int square, bool by_white) const {
        init_attack_tables_once();
        int color = color_index(by_white);
        if (g_pawn_attacks[by_white ? 1 : 0][square] & piece_bb[color][PAWN]) {
            return true;
        }
        if (g_knight_attacks[square] & piece_bb[color][KNIGHT]) {
            return true;
        }
        if (g_king_attacks[square] & piece_bb[color][KING]) {
            return true;
        }
        if (bishop_attacks(square, occ_all) & (piece_bb[color][BISHOP] | piece_bb[color][QUEEN])) {
            return true;
        }
        if (rook_attacks(square, occ_all) & (piece_bb[color][ROOK] | piece_bb[color][QUEEN])) {
            return true;
        }
        return false;
    }

    bool in_check(bool white) const {
        int king = king_square(white);
        return king != -1 && is_square_attacked(king, !white);
    }

    void generate_legal_moves(std::vector<Move> &moves) {
        std::vector<Move> pseudo;
        generate_pseudo_moves(pseudo);
        moves.clear();
        bool side = white_to_move;
        for (const Move &move : pseudo) {
            UndoState undo;
            make_move(move, undo);
            if (!in_check(side)) {
                moves.push_back(move);
            }
            undo_move(move, undo);
        }
    }

    void generate_tactical_legal_moves(std::vector<Move> &out, bool include_quiet_checks = true) {
        out.clear();
        bool side = white_to_move;
        std::vector<Move> pseudo;
        generate_pseudo_moves(pseudo, !include_quiet_checks && !in_check(side));

        if (in_check(side)) {
            for (const Move &move : pseudo) {
                UndoState undo;
                make_move(move, undo);
                if (!in_check(side)) {
                    out.push_back(move);
                }
                undo_move(move, undo);
            }
            return;
        }

        for (const Move &move : pseudo) {
            bool capture = is_capture(move);
            if (!capture) {
                if (!include_quiet_checks) {
                    continue;
                }
                UndoState undo;
                make_move(move, undo);
                bool legal = !in_check(side);
                bool gives_chk = legal && in_check(!side);
                undo_move(move, undo);
                if (gives_chk) {
                    out.push_back(move);
                }
                continue;
            }

            UndoState undo;
            make_move(move, undo);
            if (!in_check(side)) {
                out.push_back(move);
            }
            undo_move(move, undo);
        }
    }

    bool is_capture(const Move &move) const {
        if (move.is_en_passant) {
            return true;
        }
        return squares[move.to] != EMPTY;
    }

    bool gives_check(const Move &move) {
        UndoState undo;
        bool mover = white_to_move;
        make_move(move, undo);
        bool check = in_check(!mover);
        undo_move(move, undo);
        return check;
    }

    bool is_checkmate() {
        bool side = white_to_move;
        if (!in_check(side)) {
            return false;
        }
        std::vector<Move> moves;
        generate_legal_moves(moves);
        return moves.empty();
    }

    bool is_stalemate() {
        bool side = white_to_move;
        if (in_check(side)) {
            return false;
        }
        std::vector<Move> moves;
        generate_legal_moves(moves);
        return moves.empty();
    }

    void make_move(const Move &move, UndoState &undo) {
        undo.captured_piece = move.is_en_passant ? squares[white_to_move ? move.to - 8 : move.to + 8] : squares[move.to];
        undo.moved_piece = squares[move.from];
        undo.castling_rights = castling_rights;
        undo.ep_square = ep_square;
        undo.halfmove_clock = halfmove_clock;
        undo.fullmove_number = fullmove_number;
        undo.white_to_move = white_to_move;
        undo.hash_key = hash_key;
        undo.position_play_valid = position_play_valid;
        undo.position_play_cache = position_play_cache;
        hash_key = modern_hash_after_move(*this, move);

        int piece = squares[move.from];
        remove_piece_state(move.from, piece);
        squares[move.from] = EMPTY;

        if (move.is_en_passant) {
            int captured_square = white_to_move ? move.to - 8 : move.to + 8;
            remove_piece_state(captured_square, squares[captured_square]);
            squares[captured_square] = EMPTY;
        } else if (undo.captured_piece != EMPTY) {
            remove_piece_state(move.to, undo.captured_piece);
        }

        if (move.is_castling) {
            if (move.to == square_from_string("g1")) {
                move_piece_state(square_from_string("h1"), square_from_string("f1"), squares[square_from_string("h1")]);
                squares[square_from_string("f1")] = squares[square_from_string("h1")];
                squares[square_from_string("h1")] = EMPTY;
            } else if (move.to == square_from_string("c1")) {
                move_piece_state(square_from_string("a1"), square_from_string("d1"), squares[square_from_string("a1")]);
                squares[square_from_string("d1")] = squares[square_from_string("a1")];
                squares[square_from_string("a1")] = EMPTY;
            } else if (move.to == square_from_string("g8")) {
                move_piece_state(square_from_string("h8"), square_from_string("f8"), squares[square_from_string("h8")]);
                squares[square_from_string("f8")] = squares[square_from_string("h8")];
                squares[square_from_string("h8")] = EMPTY;
            } else if (move.to == square_from_string("c8")) {
                move_piece_state(square_from_string("a8"), square_from_string("d8"), squares[square_from_string("a8")]);
                squares[square_from_string("d8")] = squares[square_from_string("a8")];
                squares[square_from_string("a8")] = EMPTY;
            }
        }

        if (move.promotion != EMPTY) {
            piece = make_piece(white_to_move, move.promotion);
        }
        squares[move.to] = piece;
        add_piece_state(move.to, piece);

        ep_square = -1;
        if (piece_type(piece) == PAWN && std::abs(rank_of(move.to) - rank_of(move.from)) == 2) {
            ep_square = white_to_move ? move.from + 8 : move.from - 8;
        }

        update_castling_rights(move, piece, undo.captured_piece);

        if (piece_type(piece) == PAWN || undo.captured_piece != EMPTY) {
            halfmove_clock = 0;
        } else {
            ++halfmove_clock;
        }
        if (!white_to_move) {
            ++fullmove_number;
        }
        white_to_move = !white_to_move;
        position_play_valid = false;
    }

    void undo_move(const Move &move, const UndoState &undo) {
        white_to_move = undo.white_to_move;
        castling_rights = undo.castling_rights;
        ep_square = undo.ep_square;
        halfmove_clock = undo.halfmove_clock;
        fullmove_number = undo.fullmove_number;

        remove_piece_state(move.to, squares[move.to]);

        if (move.is_castling) {
            if (move.to == square_from_string("g1")) {
                move_piece_state(square_from_string("f1"), square_from_string("h1"), squares[square_from_string("f1")]);
                squares[square_from_string("h1")] = squares[square_from_string("f1")];
                squares[square_from_string("f1")] = EMPTY;
            } else if (move.to == square_from_string("c1")) {
                move_piece_state(square_from_string("d1"), square_from_string("a1"), squares[square_from_string("d1")]);
                squares[square_from_string("a1")] = squares[square_from_string("d1")];
                squares[square_from_string("d1")] = EMPTY;
            } else if (move.to == square_from_string("g8")) {
                move_piece_state(square_from_string("f8"), square_from_string("h8"), squares[square_from_string("f8")]);
                squares[square_from_string("h8")] = squares[square_from_string("f8")];
                squares[square_from_string("f8")] = EMPTY;
            } else if (move.to == square_from_string("c8")) {
                move_piece_state(square_from_string("d8"), square_from_string("a8"), squares[square_from_string("d8")]);
                squares[square_from_string("a8")] = squares[square_from_string("d8")];
                squares[square_from_string("d8")] = EMPTY;
            }
        }

        squares[move.from] = undo.moved_piece;
        add_piece_state(move.from, undo.moved_piece);
        squares[move.to] = move.is_en_passant ? EMPTY : undo.captured_piece;
        if (move.is_en_passant) {
            int captured_square = white_to_move ? move.to - 8 : move.to + 8;
            squares[captured_square] = undo.captured_piece;
            add_piece_state(captured_square, undo.captured_piece);
        } else if (undo.captured_piece != EMPTY) {
            add_piece_state(move.to, undo.captured_piece);
        }

        hash_key = undo.hash_key;
        position_play_valid = undo.position_play_valid;
        position_play_cache = undo.position_play_cache;
    }

    std::optional<Move> parse_uci_move(const std::string &text) {
        std::vector<Move> moves;
        generate_legal_moves(moves);
        for (const Move &move : moves) {
            if (move_to_uci(move) == text) {
                return move;
            }
        }
        return std::nullopt;
    }

  public:
    static int color_index(bool white) {
        return white ? 0 : 1;
    }

    void clear_piece_lists() {
        for (auto &side : piece_count) {
            side.fill(0);
        }
        for (auto &side : piece_bb) {
            side.fill(0);
        }
        occ.fill(0);
        occ_all = 0;
        for (auto &side : piece_list) {
            for (auto &kind : side) {
                kind.fill(-1);
            }
        }
        piece_slot.fill(-1);
        king_sq = {-1, -1};
    }

    void rebuild_piece_lists() {
        clear_piece_lists();
        for (int square = 0; square < 64; ++square) {
            int piece = squares[square];
            if (piece == EMPTY) {
                continue;
            }
            int color = color_index(is_white_piece(piece));
            int type = piece_type(piece);
            int slot = piece_count[color][type]++;
            if (slot >= kPieceListCap) {
                piece_count[color][type] = kPieceListCap;
                continue;
            }
            piece_list[color][type][slot] = square;
            piece_bb[color][type] |= bit_for(square);
            occ[color] |= bit_for(square);
            occ_all |= bit_for(square);
            piece_slot[square] = slot;
            if (type == KING) {
                king_sq[color] = square;
            }
        }
    }

    void add_piece_state(int square, int piece) {
        if (piece == EMPTY) {
            return;
        }
        int color = color_index(is_white_piece(piece));
        int type = piece_type(piece);
        if (piece_count[color][type] >= kPieceListCap) {
            rebuild_piece_lists();
        }
        int slot = piece_count[color][type]++;
        if (slot >= kPieceListCap) {
            return;
        }
        piece_list[color][type][slot] = square;
        piece_bb[color][type] |= bit_for(square);
        occ[color] |= bit_for(square);
        occ_all |= bit_for(square);
        piece_slot[square] = slot;
        if (type == KING) {
            king_sq[color] = square;
        }
    }

    void remove_piece_state(int square, int piece) {
        if (piece == EMPTY) {
            return;
        }
        int color = color_index(is_white_piece(piece));
        int type = piece_type(piece);
        int slot = piece_slot[square];
        if (slot < 0 || slot >= piece_count[color][type]) {
            rebuild_piece_lists();
            slot = piece_slot[square];
            if (slot < 0 || slot >= piece_count[color][type]) {
                return;
            }
        }
        int last_idx = --piece_count[color][type];
        int last_sq = piece_list[color][type][last_idx];
        piece_list[color][type][slot] = last_sq;
        piece_slot[last_sq] = slot;
        piece_slot[square] = -1;
        piece_bb[color][type] &= ~bit_for(square);
        occ[color] &= ~bit_for(square);
        occ_all &= ~bit_for(square);
        if (type == KING) {
            king_sq[color] = -1;
        }
    }

    void move_piece_state(int from, int to, int piece) {
        if (piece == EMPTY) {
            return;
        }
        int color = color_index(is_white_piece(piece));
        int type = piece_type(piece);
        int slot = piece_slot[from];
        if (slot < 0 || slot >= piece_count[color][type]) {
            rebuild_piece_lists();
            slot = piece_slot[from];
            if (slot < 0 || slot >= piece_count[color][type]) {
                return;
            }
        }
        piece_list[color][type][slot] = to;
        piece_bb[color][type] &= ~bit_for(from);
        piece_bb[color][type] |= bit_for(to);
        occ[color] &= ~bit_for(from);
        occ[color] |= bit_for(to);
        occ_all &= ~bit_for(from);
        occ_all |= bit_for(to);
        piece_slot[to] = slot;
        piece_slot[from] = -1;
        if (type == KING) {
            king_sq[color] = to;
        }
    }

  private:
    void update_castling_rights(const Move &move, int moved_piece, int captured_piece) {
        auto clear_if_on = [&](int square) {
            if (square == square_from_string("a1")) {
                castling_rights &= ~WHITE_QUEENSIDE;
            } else if (square == square_from_string("h1")) {
                castling_rights &= ~WHITE_KINGSIDE;
            } else if (square == square_from_string("a8")) {
                castling_rights &= ~BLACK_QUEENSIDE;
            } else if (square == square_from_string("h8")) {
                castling_rights &= ~BLACK_KINGSIDE;
            }
        };

        if (piece_type(moved_piece) == KING) {
            if (is_white_piece(moved_piece)) {
                castling_rights &= ~(WHITE_KINGSIDE | WHITE_QUEENSIDE);
            } else {
                castling_rights &= ~(BLACK_KINGSIDE | BLACK_QUEENSIDE);
            }
        }
        if (piece_type(moved_piece) == ROOK) {
            clear_if_on(move.from);
        }
        if (captured_piece != EMPTY) {
            clear_if_on(move.to);
        }
    }

    void generate_pseudo_moves(std::vector<Move> &moves, bool captures_only = false) {
        moves.clear();
        int color = color_index(white_to_move);
        for (int idx = 0; idx < piece_count[color][PAWN]; ++idx) {
            generate_pawn_moves(piece_list[color][PAWN][idx], moves, captures_only);
        }
        for (int idx = 0; idx < piece_count[color][KNIGHT]; ++idx) {
            generate_leaper_moves(piece_list[color][KNIGHT][idx], moves, KNIGHT, captures_only);
        }
        for (int idx = 0; idx < piece_count[color][BISHOP]; ++idx) {
            generate_slider_moves(piece_list[color][BISHOP][idx], moves, true, false, captures_only);
        }
        for (int idx = 0; idx < piece_count[color][ROOK]; ++idx) {
            generate_slider_moves(piece_list[color][ROOK][idx], moves, false, true, captures_only);
        }
        for (int idx = 0; idx < piece_count[color][QUEEN]; ++idx) {
            generate_slider_moves(piece_list[color][QUEEN][idx], moves, true, true, captures_only);
        }
        for (int idx = 0; idx < piece_count[color][KING]; ++idx) {
            int square = piece_list[color][KING][idx];
            generate_leaper_moves(square, moves, KING, captures_only);
            if (!captures_only) {
                generate_castling_moves(square, moves);
            }
        }
    }

    void add_promotion_moves(int from, int to, bool is_capture, std::vector<Move> &moves) {
        (void)is_capture;
        for (int promo : {QUEEN, ROOK, BISHOP, KNIGHT}) {
            Move move{from, to, promo, false, false};
            moves.push_back(move);
        }
    }

    void generate_pawn_moves(int square, std::vector<Move> &moves, bool captures_only = false) {
        bool white = white_to_move;
        int dir = white ? 8 : -8;
        int start_rank = white ? 1 : 6;
        int promotion_rank = white ? 6 : 1;
        int rank = rank_of(square);
        int own = color_index(white);
        int enemy = own ^ 1;

        if (!captures_only) {
            int one = square + dir;
            if (on_board(one) && squares[one] == EMPTY) {
                if (rank == promotion_rank) {
                    add_promotion_moves(square, one, false, moves);
                } else {
                    moves.push_back(Move{square, one, EMPTY, false, false});
                    int two = square + 2 * dir;
                    if (rank == start_rank && squares[two] == EMPTY) {
                        moves.push_back(Move{square, two, EMPTY, false, false});
                    }
                }
            }
        }

        Bitboard captures = g_pawn_attacks[own][square] & occ[enemy];
        while (captures) {
            int to = pop_lsb(captures);
            if (rank == promotion_rank) {
                add_promotion_moves(square, to, true, moves);
            } else {
                moves.push_back(Move{square, to, EMPTY, false, false});
            }
        }
        if (ep_square != -1 && (g_pawn_attacks[own][square] & bit_for(ep_square))) {
            moves.push_back(Move{square, ep_square, EMPTY, true, false});
        }
    }

    void generate_leaper_moves(int square, std::vector<Move> &moves, int type, bool captures_only = false) {
        int own = color_index(white_to_move);
        int enemy = own ^ 1;
        Bitboard targets = (type == KNIGHT ? g_knight_attacks[square] : g_king_attacks[square]) & ~occ[own];
        if (captures_only) {
            targets &= occ[enemy];
        }
        while (targets) {
            int to = pop_lsb(targets);
            moves.push_back(Move{square, to, EMPTY, false, false});
        }
    }

    void generate_slider_moves(int square, std::vector<Move> &moves, bool diagonal, bool orthogonal, bool captures_only = false) {
        int own = color_index(white_to_move);
        int enemy = own ^ 1;
        Bitboard attacks = 0;
        if (diagonal) {
            attacks |= bishop_attacks(square, occ_all);
        }
        if (orthogonal) {
            attacks |= rook_attacks(square, occ_all);
        }
        attacks &= ~occ[own];
        if (captures_only) {
            attacks &= occ[enemy];
        }
        while (attacks) {
            int to = pop_lsb(attacks);
            moves.push_back(Move{square, to, EMPTY, false, false});
        }
    }

    void generate_castling_moves(int square, std::vector<Move> &moves) {
        bool white = white_to_move;
        if (white) {
            if ((castling_rights & WHITE_KINGSIDE) &&
                squares[square_from_string("f1")] == EMPTY &&
                squares[square_from_string("g1")] == EMPTY &&
                !is_square_attacked(square_from_string("e1"), false) &&
                !is_square_attacked(square_from_string("f1"), false) &&
                !is_square_attacked(square_from_string("g1"), false)) {
                moves.push_back(Move{square, square_from_string("g1"), EMPTY, false, true});
            }
            if ((castling_rights & WHITE_QUEENSIDE) &&
                squares[square_from_string("d1")] == EMPTY &&
                squares[square_from_string("c1")] == EMPTY &&
                squares[square_from_string("b1")] == EMPTY &&
                !is_square_attacked(square_from_string("e1"), false) &&
                !is_square_attacked(square_from_string("d1"), false) &&
                !is_square_attacked(square_from_string("c1"), false)) {
                moves.push_back(Move{square, square_from_string("c1"), EMPTY, false, true});
            }
        } else {
            if ((castling_rights & BLACK_KINGSIDE) &&
                squares[square_from_string("f8")] == EMPTY &&
                squares[square_from_string("g8")] == EMPTY &&
                !is_square_attacked(square_from_string("e8"), true) &&
                !is_square_attacked(square_from_string("f8"), true) &&
                !is_square_attacked(square_from_string("g8"), true)) {
                moves.push_back(Move{square, square_from_string("g8"), EMPTY, false, true});
            }
            if ((castling_rights & BLACK_QUEENSIDE) &&
                squares[square_from_string("d8")] == EMPTY &&
                squares[square_from_string("c8")] == EMPTY &&
                squares[square_from_string("b8")] == EMPTY &&
                !is_square_attacked(square_from_string("e8"), true) &&
                !is_square_attacked(square_from_string("d8"), true) &&
                !is_square_attacked(square_from_string("c8"), true)) {
                moves.push_back(Move{square, square_from_string("c8"), EMPTY, false, true});
            }
        }
    }
};

#include "modern.cpp"

class Engine {
  public:
    int depth_opt = 3;
    int qdepth_opt = 8;
    bool modern_search_opt = false;
    int hash_mb_opt = 16;

    Board board;
    ModernSearchState modern;

    void set_hash_mb(int hash_mb) {
        hash_mb_opt = std::clamp(hash_mb, 1, 512);
        modern.resize_tt(hash_mb_opt);
    }

    void reset_for_new_game() {
        board.set_startpos();
        modern.clear_tt();
    }

    double static_move_score(Board &b, const Move &move) {
        bool mover = b.white_to_move;
        double before = position_play(b);
        Board before_board = b;
        UndoState undo;
        b.make_move(move, undo);
        double after = position_play(b);
        double bonus = move_bonus(b, move, mover, before_board);
        b.undo_move(move, undo);
        return relative_to_mover(mover, after - before) + bonus;
    }

    SearchResult analyse_move(Board &b, const Move &move, int depth, int qdepth) {
        double static_score = static_move_score(b, move);
        (void)static_score;
        UndoState undo;
        b.make_move(move, undo);
        SearchResult result = search(b, depth - 1, -kInf, kInf, qdepth);
        b.undo_move(move, undo);
        result.score = relative_to_mover(undo.white_to_move, result.score - absolute_score(b));
        result.pv.insert(result.pv.begin(), move);
        return result;
    }

    Move best_move(Board &b, int depth, int qdepth, std::vector<Move> *pv_out = nullptr, double *score_out = nullptr) {
        if (modern_search_opt) {
            return best_move_modern(b, depth, qdepth, pv_out, score_out);
        }

        std::vector<Move> moves;
        b.generate_legal_moves(moves);
        if (moves.empty()) {
            return Move{};
        }

        std::stable_sort(moves.begin(), moves.end(), [&](const Move &lhs, const Move &rhs) {
            return static_move_score(b, lhs) > static_move_score(b, rhs);
        });
        if (!b.white_to_move) {
            std::reverse(moves.begin(), moves.end());
        }
        Move best = moves.front();
        double best_score = b.white_to_move ? -kInf : kInf;
        std::vector<Move> best_pv;

        for (const Move &move : moves) {
            UndoState undo;
            b.make_move(move, undo);
            SearchResult result = search(b, depth - 1, -kInf, kInf, qdepth);
            b.undo_move(move, undo);

            if ((undo.white_to_move && result.score > best_score) || (!undo.white_to_move && result.score < best_score)) {
                best_score = result.score;
                best = move;
                best_pv = result.pv;
                best_pv.insert(best_pv.begin(), move);
            }
        }

        if (pv_out) {
            *pv_out = best_pv;
        }
        if (score_out) {
            *score_out = relative_to_mover(b.white_to_move, best_score - absolute_score(b));
        }
        return best;
    }

  private:
    struct ScoredMove {
        Move move{};
        double score = 0.0;
    };

    struct NullMoveState {
        int ep_square = -1;
        int halfmove_clock = 0;
        int fullmove_number = 1;
        bool white_to_move = true;
        std::uint64_t hash_key = 0;
    };

    static double relative_to_mover(bool white, double score) {
        return white ? score : -score;
    }

    static int piece_order_score(int type) {
        switch (type) {
            case PAWN:
                return 100;
            case KNIGHT:
                return 300;
            case BISHOP:
                return 350;
            case ROOK:
                return 500;
            case QUEEN:
                return 1000;
            default:
                return 0;
        }
    }

    Bitboard attackers_to_square(
        int square,
        int color,
        Bitboard occ_all_bits,
        const std::array<std::array<Bitboard, 7>, 2> &bbs
    ) const {
        Bitboard attackers = 0;
        attackers |= g_pawn_attacks[color == 0 ? 1 : 0][square] & bbs[color][PAWN];
        attackers |= g_knight_attacks[square] & bbs[color][KNIGHT];
        attackers |= g_king_attacks[square] & bbs[color][KING];
        attackers |= bishop_attacks(square, occ_all_bits) & (bbs[color][BISHOP] | bbs[color][QUEEN]);
        attackers |= rook_attacks(square, occ_all_bits) & (bbs[color][ROOK] | bbs[color][QUEEN]);
        return attackers;
    }

    int least_valuable_attacker_square(
        Bitboard attackers,
        const std::array<std::array<Bitboard, 7>, 2> &bbs,
        int color,
        int &type_out
    ) const {
        for (int type = PAWN; type <= KING; ++type) {
            Bitboard candidates = attackers & bbs[color][type];
            if (candidates) {
                type_out = type;
                return lsb_square(candidates);
            }
        }
        type_out = EMPTY;
        return -1;
    }

    double see_score(const Board &b, const Move &move) const {
        if (!b.is_capture(move) && move.promotion == EMPTY) {
            return 0.0;
        }

        auto bbs = b.piece_bb;
        auto occ_side = b.occ;
        Bitboard occ_all_bits = b.occ_all;

        const int stm = b.white_to_move ? 0 : 1;
        const int enemy = stm ^ 1;
        const int moving_type = piece_type(b.squares[move.from]);
        const int placed_type = move.promotion != EMPTY ? move.promotion : moving_type;
        const int captured_type = move.is_en_passant ? PAWN : piece_type(b.squares[move.to]);
        if (moving_type == EMPTY || captured_type == EMPTY) {
            return 0.0;
        }

        std::array<double, 32> gain{};
        gain[0] = kPieceValues[captured_type];
        if (move.promotion != EMPTY) {
            gain[0] += kPieceValues[placed_type] - kPieceValues[PAWN];
        }

        Bitboard from_bb = bit_for(move.from);
        bbs[stm][moving_type] &= ~from_bb;
        occ_side[stm] &= ~from_bb;
        occ_all_bits &= ~from_bb;

        if (move.is_en_passant) {
            int cap_sq = b.white_to_move ? move.to - 8 : move.to + 8;
            Bitboard cap_bb = bit_for(cap_sq);
            bbs[enemy][PAWN] &= ~cap_bb;
            occ_side[enemy] &= ~cap_bb;
            occ_all_bits &= ~cap_bb;
        } else {
            Bitboard cap_bb = bit_for(move.to);
            bbs[enemy][captured_type] &= ~cap_bb;
            occ_side[enemy] &= ~cap_bb;
            occ_all_bits &= ~cap_bb;
        }

        double current_value = kPieceValues[placed_type];
        int depth = 0;
        int side = enemy;
        while (true) {
            Bitboard attackers = attackers_to_square(move.to, side, occ_all_bits, bbs);
            if (!attackers) {
                break;
            }

            int attacker_type = EMPTY;
            int attacker_sq = least_valuable_attacker_square(attackers, bbs, side, attacker_type);
            if (attacker_sq == -1) {
                break;
            }

            ++depth;
            gain[depth] = current_value - gain[depth - 1];
            if (std::max(-gain[depth - 1], gain[depth]) < 0.0) {
                break;
            }

            Bitboard attacker_bb = bit_for(attacker_sq);
            bbs[side][attacker_type] &= ~attacker_bb;
            occ_side[side] &= ~attacker_bb;
            occ_all_bits &= ~attacker_bb;
            current_value = kPieceValues[attacker_type];
            side ^= 1;
        }

        while (depth > 0) {
            gain[depth - 1] = -std::max(-gain[depth - 1], gain[depth]);
            --depth;
        }

        return gain[0];
    }

    template <typename ScoreFn>
    void sort_moves_by_score(Board &b, std::vector<Move> &moves, ScoreFn score_fn) {
        std::vector<ScoredMove> scored;
        scored.reserve(moves.size());
        for (const auto &move : moves) {
            scored.push_back(ScoredMove{move, score_fn(move)});
        }

        for (std::size_t i = 1; i < scored.size(); ++i) {
            ScoredMove cur = scored[i];
            std::size_t j = i;
            while (j > 0 && scored[j - 1].score < cur.score) {
                scored[j] = scored[j - 1];
                --j;
            }
            scored[j] = cur;
        }

        moves.clear();
        moves.reserve(scored.size());
        for (const auto &entry : scored) {
            moves.push_back(entry.move);
        }
        if (!b.white_to_move) {
            std::reverse(moves.begin(), moves.end());
        }
    }

    int modern_order_score(Board &b, const Move &move, int ply) {
        int score = 0;
        int moved_piece = b.squares[move.from];
        int moved_type = piece_type(moved_piece);

        if (b.is_capture(move)) {
            int captured_piece = move.is_en_passant ? b.squares[b.white_to_move ? (move.to - 8) : (move.to + 8)] : b.squares[move.to];
            score += 100000;
            score += 32 * piece_order_score(piece_type(captured_piece));
            score -= piece_order_score(moved_type);
        } else {
            score += modern.killer_bonus(ply, move);
            score += modern.history_bonus(b.white_to_move, move);
        }

        if (move.promotion != EMPTY) {
            score += 12000 + piece_order_score(move.promotion);
        }
        if (move.is_castling) {
            score += 2500;
        }
        return score;
    }

    bool has_non_pawn_material(const Board &b, bool white) const {
        int color = Board::color_index(white);
        return b.piece_count[color][KNIGHT] > 0 ||
               b.piece_count[color][BISHOP] > 0 ||
               b.piece_count[color][ROOK] > 0 ||
               b.piece_count[color][QUEEN] > 0;
    }

    void make_null_move(Board &b, NullMoveState &undo) {
        init_hash_keys_once();
        undo.ep_square = b.ep_square;
        undo.halfmove_clock = b.halfmove_clock;
        undo.fullmove_number = b.fullmove_number;
        undo.white_to_move = b.white_to_move;
        undo.hash_key = b.hash_key;

        b.hash_key ^= g_side_key;
        b.hash_key ^= g_ep_keys[ep_key_idx(b.ep_square)];
        b.hash_key ^= g_ep_keys[ep_key_idx(-1)];
        b.ep_square = -1;
        ++b.halfmove_clock;
        if (!b.white_to_move) {
            ++b.fullmove_number;
        }
        b.white_to_move = !b.white_to_move;
    }

    void undo_null_move(Board &b, const NullMoveState &undo) {
        b.ep_square = undo.ep_square;
        b.halfmove_clock = undo.halfmove_clock;
        b.fullmove_number = undo.fullmove_number;
        b.white_to_move = undo.white_to_move;
        b.hash_key = undo.hash_key;
    }

    double capture_delta(Board &b, const Move &move) const {
        double gain = 0.0;
        if (b.is_capture(move)) {
            int captured_piece = move.is_en_passant ? PAWN : piece_type(b.squares[move.to]);
            gain += kPieceValues[captured_piece];
        }
        if (move.promotion != EMPTY) {
            gain += kPieceValues[move.promotion] - kPieceValues[PAWN];
        }
        return gain;
    }

    void order_moves_modern(Board &b, std::vector<Move> &moves, int ply, const Move *tt_move = nullptr) {
        sort_moves_by_score(b, moves, [&](const Move &mv) {
            return static_cast<double>(modern_order_score(b, mv, ply));
        });
        if (tt_move) {
            modern.promote_tt_move(moves, *tt_move);
        }
    }

    Move best_move_modern(Board &b, int depth, int qdepth, std::vector<Move> *pv_out, double *score_out) {
        modern.clear_ordering();

        std::vector<Move> root_moves;
        b.generate_legal_moves(root_moves);
        if (root_moves.empty()) {
            return Move{};
        }

        sort_moves_by_score(b, root_moves, [&](const Move &mv) {
            return static_move_score(b, mv);
        });

        const auto root_key = b.hash_key;
        Move best = root_moves.front();
        double best_score = b.white_to_move ? -kInf : kInf;
        std::vector<Move> best_pv;

        for (int cur_depth = 1; cur_depth <= depth; ++cur_depth) {
            const auto *root_tt = modern.probe(root_key);
            if (root_tt && root_tt->has_move) {
                modern.promote_tt_move(root_moves, root_tt->best_move);
            } else if (cur_depth > 1) {
                modern.promote_tt_move(root_moves, best);
            }

            Move iter_best = root_moves.front();
            double iter_best_score = b.white_to_move ? -kInf : kInf;
            std::vector<Move> iter_best_pv;

            for (const Move &move : root_moves) {
                UndoState undo;
                b.make_move(move, undo);
                SearchResult result = search_modern(b, cur_depth - 1, -kInf, kInf, qdepth, 1);
                b.undo_move(move, undo);

                if ((undo.white_to_move && result.score > iter_best_score) || (!undo.white_to_move && result.score < iter_best_score)) {
                    iter_best_score = result.score;
                    iter_best = move;
                    iter_best_pv = result.pv;
                    iter_best_pv.insert(iter_best_pv.begin(), move);
                }
            }

            best = iter_best;
            best_score = iter_best_score;
            best_pv = iter_best_pv;
            modern.store(root_key, cur_depth, best_score, BOUND_EXACT, &best);
            modern.promote_tt_move(root_moves, best);
        }

        if (pv_out) {
            *pv_out = best_pv;
        }
        if (score_out) {
            *score_out = relative_to_mover(b.white_to_move, best_score - absolute_score(b));
        }
        return best;
    }

    double absolute_score(Board &b) {
        if (b.is_checkmate()) {
            return b.white_to_move ? -kMateScore : kMateScore;
        }
        if (b.is_stalemate()) {
            return 0.0;
        }

        double score = position_play(b);
        for (int type = PAWN; type <= QUEEN; ++type) {
            score += kPieceValues[type] * b.piece_count[0][type];
            score -= kPieceValues[type] * b.piece_count[1][type];
        }
        return score;
    }

    double position_play(Board &b) {
        if (!b.position_play_valid) {
            b.position_play_cache = compute_position_play(b);
            b.position_play_valid = true;
        }
        return b.position_play_cache;
    }

    double compute_position_play(Board &b) {
        return side_position_play(b, true) - side_position_play(b, false);
    }

    double side_position_play(Board &b, bool white) {
        double score = 0.0;
        int color = white ? 0 : 1;

        for (int idx = 0; idx < b.piece_count[color][QUEEN]; ++idx) {
            score += mobility_score(b, b.piece_list[color][QUEEN][idx], white);
        }
        for (int idx = 0; idx < b.piece_count[color][ROOK]; ++idx) {
            int square = b.piece_list[color][ROOK][idx];
            score += mobility_score(b, square, white);
            int defenders = attacker_count(b, square, white);
            score += defenders >= 2 ? 1.5 : defenders >= 1 ? 1.0
                                                           : 0.0;
        }
        for (int idx = 0; idx < b.piece_count[color][BISHOP]; ++idx) {
            int square = b.piece_list[color][BISHOP][idx];
            score += mobility_score(b, square, white);
            int defenders = attacker_count(b, square, white);
            score += defenders >= 2 ? 1.5 : defenders >= 1 ? 1.0
                                                           : 0.0;
        }
        for (int idx = 0; idx < b.piece_count[color][KNIGHT]; ++idx) {
            int square = b.piece_list[color][KNIGHT][idx];
            score += mobility_score(b, square, white);
            int defenders = attacker_count(b, square, white);
            score += defenders >= 2 ? 1.5 : defenders >= 1 ? 1.0
                                                           : 0.0;
        }
        for (int idx = 0; idx < b.piece_count[color][KING]; ++idx) {
            int square = b.piece_list[color][KING][idx];
            score += mobility_score(b, square, white);
            score -= king_safety_penalty(b, square, white);
        }
        for (int idx = 0; idx < b.piece_count[color][PAWN]; ++idx) {
            int square = b.piece_list[color][PAWN][idx];
            score += 0.2 * ranks_advanced(square, white);
            if (is_defended_by_non_pawn(b, square, white)) {
                score += 0.3;
            }
        }
        return score;
    }

    double mobility_score(Board &b, int square, bool white) {
        (void)white;
        int count = mobility_count(b, square);
        return count > 0 ? std::sqrt(static_cast<double>(count)) : 0.0;
    }

    int mobility_count(Board &b, int square) {
        int piece = b.squares[square];
        int type = piece_type(piece);
        int count = 0;
        int file = file_of(square);
        int rank = rank_of(square);

        auto visit = [&](int to) {
            int occupant = b.squares[to];
            if (occupant != EMPTY && piece_color(occupant) == piece_color(piece)) {
                return false;
            }
            count += (occupant != EMPTY && piece_color(occupant) != piece_color(piece)) ? 2 : 1;
            return occupant == EMPTY;
        };

        if (type == KNIGHT || type == KING) {
            static const int knight_offsets[8][2] = {
                {1, 2}, {2, 1}, {2, -1}, {1, -2},
                {-1, -2}, {-2, -1}, {-2, 1}, {-1, 2},
            };
            static const int king_offsets[8][2] = {
                {1, 0}, {1, 1}, {0, 1}, {-1, 1},
                {-1, 0}, {-1, -1}, {0, -1}, {1, -1},
            };
            const auto &offsets = (type == KNIGHT) ? knight_offsets : king_offsets;
            for (int i = 0; i < 8; ++i) {
                int nf = file + offsets[i][0];
                int nr = rank + offsets[i][1];
                if (nf >= 0 && nf < 8 && nr >= 0 && nr < 8) {
                    visit(nr * 8 + nf);
                }
            }
            return count;
        }

        auto scan = [&](int df, int dr) {
            int nf = file + df;
            int nr = rank + dr;
            while (nf >= 0 && nf < 8 && nr >= 0 && nr < 8) {
                if (!visit(nr * 8 + nf)) {
                    break;
                }
                nf += df;
                nr += dr;
            }
        };

        if (type == BISHOP || type == QUEEN) {
            scan(1, 1);
            scan(1, -1);
            scan(-1, 1);
            scan(-1, -1);
        }
        if (type == ROOK || type == QUEEN) {
            scan(1, 0);
            scan(-1, 0);
            scan(0, 1);
            scan(0, -1);
        }
        return count;
    }

    int attacker_count(Board &b, int square, bool white) {
        int color = white ? 0 : 1;
        Bitboard attackers = 0;
        attackers |= g_pawn_attacks[white ? 1 : 0][square] & b.piece_bb[color][PAWN];
        attackers |= g_knight_attacks[square] & b.piece_bb[color][KNIGHT];
        attackers |= g_king_attacks[square] & b.piece_bb[color][KING];
        attackers |= bishop_attacks(square, b.occ_all) & (b.piece_bb[color][BISHOP] | b.piece_bb[color][QUEEN]);
        attackers |= rook_attacks(square, b.occ_all) & (b.piece_bb[color][ROOK] | b.piece_bb[color][QUEEN]);
        return std::popcount(attackers);
    }

    bool attacks_square(Board &b, int from, int target, int type, bool white) {
        (void)white;
        Bitboard target_bb = bit_for(target);
        if (type == PAWN) {
            return (g_pawn_attacks[Board::color_index(is_white_piece(b.squares[from]))][from] & target_bb) != 0;
        }
        if (type == KNIGHT) {
            return (g_knight_attacks[from] & target_bb) != 0;
        }
        if (type == KING) {
            return (g_king_attacks[from] & target_bb) != 0;
        }
        if (type == BISHOP) {
            return (bishop_attacks(from, b.occ_all) & target_bb) != 0;
        }
        if (type == ROOK) {
            return (rook_attacks(from, b.occ_all) & target_bb) != 0;
        }
        if (type == QUEEN) {
            return ((bishop_attacks(from, b.occ_all) | rook_attacks(from, b.occ_all)) & target_bb) != 0;
        }
        return false;
    }

    double king_safety_penalty(Board &b, int square, bool white) {
        int saved = b.squares[square];
        b.remove_piece_state(square, saved);
        b.squares[square] = make_piece(white, QUEEN);
        b.add_piece_state(square, b.squares[square]);
        double penalty = mobility_score(b, square, white);
        b.remove_piece_state(square, b.squares[square]);
        b.squares[square] = saved;
        b.add_piece_state(square, saved);
        return penalty;
    }

    int ranks_advanced(int square, bool white) {
        int rank = rank_of(square);
        return white ? std::max(0, rank - 1) : std::max(0, 6 - rank);
    }

    bool is_defended_by_non_pawn(Board &b, int square, bool white) {
        int color = white ? 0 : 1;
        Bitboard attackers = 0;
        attackers |= g_knight_attacks[square] & b.piece_bb[color][KNIGHT];
        attackers |= g_king_attacks[square] & b.piece_bb[color][KING];
        attackers |= bishop_attacks(square, b.occ_all) & (b.piece_bb[color][BISHOP] | b.piece_bb[color][QUEEN]);
        attackers |= rook_attacks(square, b.occ_all) & (b.piece_bb[color][ROOK] | b.piece_bb[color][QUEEN]);
        return attackers != 0;
    }

    int castling_moves_mask(Board b, bool color) {
        bool saved = b.white_to_move;
        b.white_to_move = color;
        std::vector<Move> moves;
        b.generate_legal_moves(moves);
        b.white_to_move = saved;
        int mask = 0;
        for (const Move &move : moves) {
            if (!move.is_castling) {
                continue;
            }
            if (move.to == square_from_string(color ? "g1" : "g8")) {
                mask |= 1;
            } else {
                mask |= 2;
            }
        }
        return mask;
    }

    bool preserves_castling_rights(const Board &before, const Board &after, bool color) {
        int before_mask = color ? (before.castling_rights & (WHITE_KINGSIDE | WHITE_QUEENSIDE))
                                : (before.castling_rights & (BLACK_KINGSIDE | BLACK_QUEENSIDE));
        int after_mask = color ? (after.castling_rights & (WHITE_KINGSIDE | WHITE_QUEENSIDE))
                               : (after.castling_rights & (BLACK_KINGSIDE | BLACK_QUEENSIDE));
        return before_mask == after_mask && before_mask != 0;
    }

    bool has_mate_in_one_threat(Board b, bool mover) {
        bool saved = b.white_to_move;
        b.white_to_move = mover;
        std::vector<Move> moves;
        b.generate_legal_moves(moves);
        for (const Move &move : moves) {
            UndoState undo;
            b.make_move(move, undo);
            bool mate = b.is_checkmate();
            b.undo_move(move, undo);
            if (mate) {
                b.white_to_move = saved;
                return true;
            }
        }
        b.white_to_move = saved;
        return false;
    }

    double move_bonus(Board &after, const Move &move, bool mover, const Board &before) {
        double bonus = 0.0;
        int moved_piece = before.squares[move.from];
        if (move.is_castling) {
            bonus += 1.0;
        } else {
            int castle_before = castling_moves_mask(before, mover);
            int castle_after = castling_moves_mask(after, mover);
            if ((piece_type(moved_piece) == KING || piece_type(moved_piece) == ROOK) &&
                preserves_castling_rights(before, after, mover)) {
                bonus += 1.0;
            }
            if ((castle_after & ~castle_before) != 0) {
                bonus += 1.0;
            }
        }
        if (after.in_check(!mover)) {
            bonus += 0.5;
        }
        if (has_mate_in_one_threat(after, mover)) {
            bonus += 1.0;
        }
        return bonus;
    }

    double ordering_score(Board &b, const Move &move) {
        bool mover = b.white_to_move;
        double before = position_play(b);
        UndoState undo;
        b.make_move(move, undo);
        double after = position_play(b);
        double bonus = 0.0;
        if (b.in_check(!mover)) {
            bonus += 0.5;
        }
        if (move.is_castling) {
            bonus += 1.0;
        }
        b.undo_move(move, undo);
        return relative_to_mover(mover, after - before) + bonus;
    }

    SearchResult search_modern(Board &b, int depth, double alpha, double beta, int qdepth, int ply) {
        const std::uint64_t key = b.hash_key;
        if (depth <= 0) {
            return quiescence_modern(b, alpha, beta, qdepth, ply, 0);
        }

        const double alpha0 = alpha;
        const double beta0 = beta;
        const TtEntry *tt_entry = modern.probe(key);
        if (tt_entry && tt_entry->depth >= depth) {
            if (tt_entry->flag == BOUND_EXACT) {
                SearchResult hit{tt_entry->score, {}};
                if (tt_entry->has_move) {
                    hit.pv.push_back(tt_entry->best_move);
                }
                return hit;
            }
            if (tt_entry->flag == BOUND_LOWER) {
                alpha = std::max(alpha, tt_entry->score);
            } else if (tt_entry->flag == BOUND_UPPER) {
                beta = std::min(beta, tt_entry->score);
            }
            if (alpha >= beta) {
                SearchResult hit{tt_entry->score, {}};
                if (tt_entry->has_move) {
                    hit.pv.push_back(tt_entry->best_move);
                }
                return hit;
            }
        }

        const bool side_in_check = b.in_check(b.white_to_move);
        if (!side_in_check && depth >= 3 && ply > 0 && has_non_pawn_material(b, b.white_to_move)) {
            NullMoveState null_undo;
            const bool maximizing = b.white_to_move;
            const int reduction = depth >= 6 ? 3 : 2;
            make_null_move(b, null_undo);
            SearchResult null_res = search_modern(b, depth - 1 - reduction, alpha, beta, qdepth, ply + 1);
            undo_null_move(b, null_undo);
            if ((maximizing && null_res.score >= beta) || (!maximizing && null_res.score <= alpha)) {
                return {null_res.score, {}};
            }
        }

        std::vector<Move> moves;
        b.generate_legal_moves(moves);
        if (moves.empty()) {
            return {b.in_check(b.white_to_move) ? (b.white_to_move ? -kMateScore : kMateScore) : 0.0, {}};
        }
        const Move *tt_move = (tt_entry && tt_entry->has_move) ? &tt_entry->best_move : nullptr;
        order_moves_modern(b, moves, ply, tt_move);

        SearchResult best;
        best.score = b.white_to_move ? -kInf : kInf;
        Move best_move_local{};
        bool have_best_move = false;
        const bool maximizing = b.white_to_move;
        constexpr double kPvsEps = 1e-9;
        int quiet_seen = 0;
        double static_eval = 0.0;
        const bool can_futility = !side_in_check && depth <= 2;
        if (can_futility) {
            static_eval = absolute_score(b);
        }

        for (std::size_t move_idx = 0; move_idx < moves.size(); ++move_idx) {
            const Move &move = moves[move_idx];
            const bool is_quiet = !b.is_capture(move) && move.promotion == EMPTY && !move.is_castling;
            if (!side_in_check && is_quiet) {
                ++quiet_seen;
                int lmp_limit = depth == 1 ? 1 : 4;
                if (quiet_seen > lmp_limit) {
                    continue;
                }
            }
            if (can_futility && is_quiet) {
                double margin = depth == 1 ? 1.5 : 3.0;
                if ((maximizing && static_eval + margin <= alpha) ||
                    (!maximizing && static_eval - margin >= beta)) {
                    continue;
                }
            }

            UndoState undo;
            b.make_move(move, undo);
            const bool reducible = !side_in_check &&
                                   depth >= 3 &&
                                   move_idx >= 3 &&
                                   !b.is_capture(move) &&
                                   move.promotion == EMPTY &&
                                   !move.is_castling;

            SearchResult child;
            if (move_idx == 0) {
                child = search_modern(b, depth - 1, alpha, beta, qdepth, ply + 1);
            } else {
                int probe_depth = depth - 1;
                if (reducible) {
                    probe_depth = std::max(0, probe_depth - 1);
                }

                double probe_alpha = maximizing ? alpha : (beta - kPvsEps);
                double probe_beta = maximizing ? (alpha + kPvsEps) : beta;
                child = search_modern(b, probe_depth, probe_alpha, probe_beta, qdepth, ply + 1);

                bool needs_full = reducible ||
                                  (maximizing ? (child.score > alpha && child.score < beta)
                                              : (child.score < beta && child.score > alpha));
                if (needs_full) {
                    child = search_modern(b, depth - 1, alpha, beta, qdepth, ply + 1);
                }
            }
            b.undo_move(move, undo);

            if ((undo.white_to_move && child.score > best.score) || (!undo.white_to_move && child.score < best.score)) {
                best.score = child.score;
                best.pv = child.pv;
                best.pv.insert(best.pv.begin(), move);
                best_move_local = move;
                have_best_move = true;
            }

            if (undo.white_to_move) {
                alpha = std::max(alpha, best.score);
            } else {
                beta = std::min(beta, best.score);
            }
            if (alpha >= beta) {
                modern.note_cutoff(undo.white_to_move, ply, move, b.is_capture(move), depth);
                break;
            }
        }

        int flag = BOUND_EXACT;
        if (best.score <= alpha0) {
            flag = BOUND_UPPER;
        } else if (best.score >= beta0) {
            flag = BOUND_LOWER;
        }
        modern.store(key, depth, best.score, flag, have_best_move ? &best_move_local : nullptr);
        return best;
    }

    SearchResult quiescence_modern(Board &b, double alpha, double beta, int depth, int ply, int qply) {
        const std::uint64_t key = b.hash_key ^ (0xabc98388fb8fac03ULL + static_cast<std::uint64_t>(depth));
        double stand_pat = absolute_score(b);
        if (depth <= 0) {
            return {stand_pat, {}};
        }

        const double alpha0 = alpha;
        const double beta0 = beta;
        const TtEntry *tt_entry = modern.probe(key);
        if (tt_entry && tt_entry->depth >= depth) {
            if (tt_entry->flag == BOUND_EXACT) {
                SearchResult hit{tt_entry->score, {}};
                if (tt_entry->has_move) {
                    hit.pv.push_back(tt_entry->best_move);
                }
                return hit;
            }
            if (tt_entry->flag == BOUND_LOWER) {
                alpha = std::max(alpha, tt_entry->score);
            } else if (tt_entry->flag == BOUND_UPPER) {
                beta = std::min(beta, tt_entry->score);
            }
            if (alpha >= beta) {
                SearchResult hit{tt_entry->score, {}};
                if (tt_entry->has_move) {
                    hit.pv.push_back(tt_entry->best_move);
                }
                return hit;
            }
        }

        const bool side_in_check = b.in_check(b.white_to_move);

        if (b.white_to_move) {
            if (stand_pat >= beta) {
                return {stand_pat, {}};
            }
            alpha = std::max(alpha, stand_pat);
        } else {
            if (stand_pat <= alpha) {
                return {stand_pat, {}};
            }
            beta = std::min(beta, stand_pat);
        }

        std::vector<Move> tactical;
        bool include_quiet_checks = false;
        b.generate_tactical_legal_moves(tactical, include_quiet_checks);
        if (tactical.empty()) {
            return {stand_pat, {}};
        }

        const Move *tt_move = (tt_entry && tt_entry->has_move) ? &tt_entry->best_move : nullptr;
        order_moves_modern(b, tactical, ply, tt_move);

        SearchResult best{stand_pat, {}};
        Move best_move_local{};
        bool have_best_move = false;
        for (const Move &move : tactical) {
            if (!side_in_check && b.is_capture(move) && see_score(b, move) <= 0.0) {
                continue;
            }
            if (!side_in_check) {
                const double gain = capture_delta(b, move);
                constexpr double kDeltaMargin = 1.0;
                if (b.white_to_move) {
                    if (stand_pat + gain + kDeltaMargin <= alpha) {
                        continue;
                    }
                } else {
                    if (stand_pat - gain - kDeltaMargin >= beta) {
                        continue;
                    }
                }
            }

            UndoState undo;
            b.make_move(move, undo);
            SearchResult child = quiescence_modern(b, alpha, beta, depth - 1, ply + 1, qply + 1);
            b.undo_move(move, undo);

            if ((undo.white_to_move && child.score > best.score) || (!undo.white_to_move && child.score < best.score)) {
                best.score = child.score;
                best.pv = child.pv;
                best.pv.insert(best.pv.begin(), move);
                best_move_local = move;
                have_best_move = true;
            }
            if (undo.white_to_move) {
                alpha = std::max(alpha, best.score);
            } else {
                beta = std::min(beta, best.score);
            }
            if (alpha >= beta) {
                modern.note_cutoff(undo.white_to_move, ply, move, true, depth);
                break;
            }
        }

        int flag = BOUND_EXACT;
        if (best.score <= alpha0) {
            flag = BOUND_UPPER;
        } else if (best.score >= beta0) {
            flag = BOUND_LOWER;
        }
        modern.store(key, depth, best.score, flag, have_best_move ? &best_move_local : nullptr);
        return best;
    }

    SearchResult search(Board &b, int depth, double alpha, double beta, int qdepth) {
        if (b.is_checkmate() || b.is_stalemate()) {
            return {absolute_score(b), {}};
        }
        if (depth <= 0) {
            return quiescence(b, alpha, beta, qdepth, 0);
        }

        const double alpha0 = alpha;
        const double beta0 = beta;
        const auto key = modern.position_key(b);
        if (modern_search_opt) {
            const auto *tt_entry = modern.probe(key);
            if (tt_entry && tt_entry->depth >= depth) {
                if (tt_entry->flag == BOUND_EXACT) {
                    SearchResult hit{tt_entry->score, {}};
                    if (tt_entry->has_move) {
                        hit.pv.push_back(tt_entry->best_move);
                    }
                    return hit;
                }
                if (tt_entry->flag == BOUND_LOWER) {
                    alpha = std::max(alpha, tt_entry->score);
                } else if (tt_entry->flag == BOUND_UPPER) {
                    beta = std::min(beta, tt_entry->score);
                }
                if (alpha >= beta) {
                    SearchResult hit{tt_entry->score, {}};
                    if (tt_entry->has_move) {
                        hit.pv.push_back(tt_entry->best_move);
                    }
                    return hit;
                }
            }
        }

        std::vector<Move> moves;
        b.generate_legal_moves(moves);
        std::stable_sort(moves.begin(), moves.end(), [&](const Move &lhs, const Move &rhs) {
            return ordering_score(b, lhs) > ordering_score(b, rhs);
        });
        if (!b.white_to_move) {
            std::reverse(moves.begin(), moves.end());
        }
        if (modern_search_opt) {
            const auto *tt_entry = modern.probe(key);
            if (tt_entry && tt_entry->has_move) {
                modern.promote_tt_move(moves, tt_entry->best_move);
            }
        }

        SearchResult best;
        best.score = b.white_to_move ? -kInf : kInf;
        Move best_move_local{};
        bool have_best_move = false;

        for (const Move &move : moves) {
            UndoState undo;
            b.make_move(move, undo);
            SearchResult child = search(b, depth - 1, alpha, beta, qdepth);
            b.undo_move(move, undo);

            if ((undo.white_to_move && child.score > best.score) || (!undo.white_to_move && child.score < best.score)) {
                best.score = child.score;
                best.pv = child.pv;
                best.pv.insert(best.pv.begin(), move);
                best_move_local = move;
                have_best_move = true;
            }

            if (undo.white_to_move) {
                alpha = std::max(alpha, best.score);
            } else {
                beta = std::min(beta, best.score);
            }
            if (alpha >= beta) {
                break;
            }
        }
        if (modern_search_opt) {
            int flag = BOUND_EXACT;
            if (best.score <= alpha0) {
                flag = BOUND_UPPER;
            } else if (best.score >= beta0) {
                flag = BOUND_LOWER;
            }
            modern.store(key, depth, best.score, flag, have_best_move ? &best_move_local : nullptr);
        }
        return best;
    }

    SearchResult quiescence(Board &b, double alpha, double beta, int depth, int qply) {
        double stand_pat = absolute_score(b);
        if (depth <= 0) {
            return {stand_pat, {}};
        }

        const double alpha0 = alpha;
        const double beta0 = beta;
        const auto key = modern.position_key(b) ^ (0xabc98388fb8fac03ULL + static_cast<std::uint64_t>(depth));
        if (modern_search_opt) {
            const auto *tt_entry = modern.probe(key);
            if (tt_entry && tt_entry->depth >= depth) {
                if (tt_entry->flag == BOUND_EXACT) {
                    SearchResult hit{tt_entry->score, {}};
                    if (tt_entry->has_move) {
                        hit.pv.push_back(tt_entry->best_move);
                    }
                    return hit;
                }
                if (tt_entry->flag == BOUND_LOWER) {
                    alpha = std::max(alpha, tt_entry->score);
                } else if (tt_entry->flag == BOUND_UPPER) {
                    beta = std::min(beta, tt_entry->score);
                }
                if (alpha >= beta) {
                    SearchResult hit{tt_entry->score, {}};
                    if (tt_entry->has_move) {
                        hit.pv.push_back(tt_entry->best_move);
                    }
                    return hit;
                }
            }
        }

        if (b.white_to_move) {
            if (stand_pat >= beta) {
                return {stand_pat, {}};
            }
            alpha = std::max(alpha, stand_pat);
        } else {
            if (stand_pat <= alpha) {
                return {stand_pat, {}};
            }
            beta = std::min(beta, stand_pat);
        }

        std::vector<Move> tactical;
        bool include_quiet_checks = true;
        b.generate_tactical_legal_moves(tactical, include_quiet_checks);
        if (tactical.empty()) {
            return {stand_pat, {}};
        }

        std::stable_sort(tactical.begin(), tactical.end(), [&](const Move &lhs, const Move &rhs) {
            return ordering_score(b, lhs) > ordering_score(b, rhs);
        });
        if (!b.white_to_move) {
            std::reverse(tactical.begin(), tactical.end());
        }
        if (modern_search_opt) {
            const auto *tt_entry = modern.probe(key);
            if (tt_entry && tt_entry->has_move) {
                modern.promote_tt_move(tactical, tt_entry->best_move);
            }
        }

        SearchResult best{stand_pat, {}};
        Move best_move_local{};
        bool have_best_move = false;
        for (const Move &move : tactical) {
            UndoState undo;
            b.make_move(move, undo);
            SearchResult child = quiescence(b, alpha, beta, depth - 1, qply + 1);
            b.undo_move(move, undo);

            if ((undo.white_to_move && child.score > best.score) || (!undo.white_to_move && child.score < best.score)) {
                best.score = child.score;
                best.pv = child.pv;
                best.pv.insert(best.pv.begin(), move);
                best_move_local = move;
                have_best_move = true;
            }
            if (undo.white_to_move) {
                alpha = std::max(alpha, best.score);
            } else {
                beta = std::min(beta, best.score);
            }
            if (alpha >= beta) {
                break;
            }
        }
        if (modern_search_opt) {
            int flag = BOUND_EXACT;
            if (best.score <= alpha0) {
                flag = BOUND_UPPER;
            } else if (best.score >= beta0) {
                flag = BOUND_LOWER;
            }
            modern.store(key, depth, best.score, flag, have_best_move ? &best_move_local : nullptr);
        }
        return best;
    }
};

class UciApp {
  public:
    void run() {
        std::string line;
        while (std::getline(std::cin, line)) {
            if (line == "uci") {
                handle_uci();
                continue;
            }

            if (line == "isready") {
                std::cout << "readyok\n";
                continue;
            }

            if (line == "ucinewgame") {
                engine.reset_for_new_game();
                continue;
            }

            if (line.rfind("setoption", 0) == 0) {
                handle_setoption(line);
                continue;
            }

            if (line.rfind("position", 0) == 0) {
                handle_position(line);
                continue;
            }

            if (line.rfind("go", 0) == 0) {
                handle_go(line);
                continue;
            }

            if (line == "quit") {
                break;
            }
        }
    }

  private:
    Engine engine;

    void handle_uci() {
        std::cout << "id name TurochampCPP\n";
        std::cout << "id author Alan Turing\n";
        std::cout << "option name Depth type spin default 3 min 1 max 4\n";
        std::cout << "option name QSearchDepth type spin default 8 min 0 max 32\n";
        std::cout << "option name ModernSearch type check default false\n";
        std::cout << "option name HashMB type spin default 16 min 1 max 512\n";
        std::cout << "uciok\n";
    }

    void handle_setoption(const std::string &line) {
        std::istringstream ss(line);
        std::string word;
        ss >> word;
        ss >> word;

        std::string name;
        while (ss >> word && word != "value") {
            if (!name.empty()) {
                name.push_back(' ');
            }
            name += word;
        }

        if (name == "Depth") {
            int val = 0;
            ss >> val;
            engine.depth_opt = std::clamp(val, 1, kMaxDepth);
            return;
        }

        if (name == "QSearchDepth") {
            int val = 0;
            ss >> val;
            engine.qdepth_opt = std::clamp(val, 0, 32);
            return;
        }

        if (name == "ModernSearch") {
            std::string val;
            ss >> val;
            std::transform(val.begin(), val.end(), val.begin(), [](unsigned char c) {
                return static_cast<char>(std::tolower(c));
            });
            engine.modern_search_opt = (val == "true" || val == "1" || val == "on");
            return;
        }

        if (name == "HashMB") {
            int val = 0;
            ss >> val;
            engine.set_hash_mb(val);
        }
    }

    void handle_position(const std::string &line) {
        std::istringstream ss(line);
        std::string word;
        ss >> word;
        ss >> word;

        if (word == "startpos") {
            engine.board.set_startpos();
        } else if (word == "fen") {
            std::string fen;
            std::vector<std::string> fen_parts;
            // Cutechess and every normal GUI send the whole 6-field FEN here.
            for (int i = 0; i < 6 && ss >> word; ++i) {
                fen_parts.push_back(word);
            }
            for (size_t i = 0; i < fen_parts.size(); ++i) {
                if (i) {
                    fen.push_back(' ');
                }
                fen += fen_parts[i];
            }
            engine.board.set_fen(fen);
        }

        if (!(ss >> word)) {
            return;
        }
        if (word != "moves") {
            return;
        }

        while (ss >> word) {
            std::optional<Move> move = engine.board.parse_uci_move(word);
            if (move) {
                UndoState undo;
                engine.board.make_move(*move, undo);
            }
        }
    }

    void handle_go(const std::string &line) {
        std::istringstream ss(line);
        std::string word;
        ss >> word;

        int depth = engine.depth_opt;
        while (ss >> word) {
            if (word == "depth") {
                ss >> depth;
            }
        }
        depth = std::clamp(depth, 1, kMaxDepth);

        // TODO: if we keep this engine around, hook up clocks instead of pretending fixed-depth is enough.
        std::vector<Move> pv;
        double score = 0.0;
        Move best = engine.best_move(engine.board, depth, engine.qdepth_opt, &pv, &score);
        std::cout << "info depth " << depth << " score cp " << static_cast<int>(std::round(score * 100.0)) << " pv";
        for (const Move &move : pv) {
            std::cout << ' ' << move_to_uci(move);
        }
        std::cout << "\n";
        std::cout << "bestmove " << move_to_uci(best) << "\n";
    }
};

}  // namespace

int main() {
    UciApp app;
    app.run();
    return 0;
}
