(** * Spec.PngModel.Trees — transcription of zlib-1.3.1's [trees.c].

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.  Depends on
    [Spec.PngModel.{Base, ZBitsOut, Chunk}] and Stdlib.

    Source: [materials/zlib-1.3.1/trees.c] (in-container
    [/harness/problem/materials/zlib-1.3.1/trees.c]) together with the
    parts of [deflate.h] that [trees.c] uses ([ct_data], [HEAP_SIZE],
    [d_code], the [_tr_tally_*] inline macros).  This is a BUG-FOR-BUG
    transcription of the code the delivered binary was built from — plain
    [gcc -O2], stock [./configure --static], so
    [ZLIB_DEBUG], [GEN_TREES_H], [LIT_MEM], [FASTEST], [FORCE_STATIC] and
    [FORCE_STORED] are all OFF and [STDC] is ON.  Consequences pinned here:

    - [tr_static_init] is a NO-OP ([trees.c:294-373] is entirely inside
      [#if defined(GEN_TREES_H) || !defined(STDC)]); the static trees and
      the [_dist_code]/[_length_code]/[base_length]/[base_dist] tables come
      from the pre-generated [trees.h] and are transcribed verbatim below
      (generated from [trees.h] by [wp4work/wp4d/gen_tables.py], not typed
      by hand).
    - [send_bits] is the MACRO at [trees.c:273-285], not the [ZLIB_DEBUG]
      function; the macro evaluates [length] once but [value] twice on the
      no-split path — harmless here since every call site passes a
      side-effect-free expression, as the C comment at [:289] demands.
    - [LIT_MEM] off means the [sym_buf] layout ([trees.c:911-914],
      [deflate.h:351-369]): three bytes per symbol, [dist] little-endian
      in the first two, [lc] in the third.

    Machine-integer widths, transcribed explicitly ([zutil.h:39-43]):
    [uch] = [u8], [ush] = [u16], [ulg] = [unsigned long] = 64 bits on
    riscv64 LP64, so [opt_len]/[static_len] use [u64].  That last one is
    not cosmetic: [build_tree]'s forced-two-codes loop ([trees.c:653-659])
    does [s->opt_len--] on a [ulg] that can legitimately be 0, and the
    resulting [2^64 - 1] then decides [_tr_flush_block]'s
    stored/static/dynamic comparison.

    The [ct_data] UNION is modelled faithfully ([deflate.h:72-86]): one
    16-bit slot holds [Freq] OR [Code], the other holds [Dad] OR [Len].
    [gen_bitlen] relies on this ("We overwrite tree[n].Dad which is no
    longer needed", [trees.c:564]) and [gen_codes] overwrites [Freq] with
    [Code], so a two-array [Tree] with aliased accessors is the only
    faithful representation.

    Structure, chosen so a machine-level walk can cut where the C cuts
    (c5-invariants.md §3.6):

    - every C loop is a [nat]-fuelled [Fixpoint] whose fuel is a static
      bound read off the same loop;
    - the two loops a walk wants to index by trip count ([build_tree]'s
      combine loop and [compress_block]'s emit loop) additionally get the
      [_step] / [Cont|Break] / [_iter] / [_iter_loop] treatment that
      [Inftrees.v] uses for [inflate_table]'s fill loop;
    - [tr_wf] collects the caller obligations.

    QUARANTINE (c5-invariants.md §2.2).  [_tr_flush_block]'s
    stored/static/dynamic size comparison is a HEURISTIC: it is transcribed
    exactly (a refinement proof needs it) but no optimality claim is made
    or needed.  The round-trip theorem is proved for any block choice.
    The three token contracts the round-trip lane consumes ([cEnc],
    [cEmpty], [cRes]) are stated at the end of this file.

    Validated against the delivered binary: see [a working folder]
    (R1 boundary records for [build_tree] and [_tr_flush_block] from
    [/harness/reference_binary] under qemu GDB-RSP, plus injected stress). *)

From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base ZBitsOut Chunk.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

(** ** 1. Constants *)

(** [deflate.h:34-56]. *)
Definition LENGTH_CODES : Z := 29.
Definition LITERALS     : Z := 256.
Definition L_CODES      : Z := 286.   (** [LITERALS+1+LENGTH_CODES] *)
Definition D_CODES      : Z := 30.
Definition BL_CODES     : Z := 19.
Definition HEAP_SIZE    : Z := 573.   (** [2*L_CODES+1] *)
Definition MAX_BITS     : Z := 15.

(** [trees.c:47-60]. *)
Definition MAX_BL_BITS  : Z := 7.
Definition END_BLOCK    : Z := 256.
Definition REP_3_6      : Z := 16.
Definition REPZ_3_10    : Z := 17.
Definition REPZ_11_138  : Z := 18.
Definition DIST_CODE_LEN : Z := 512.  (** [trees.c:81] *)
Definition SMALLEST     : Z := 1.     (** [trees.c:478] *)

(** [zutil.h:79-81]. *)
Definition STORED_BLOCK : Z := 0.
Definition STATIC_TREES : Z := 1.
Definition DYN_TREES    : Z := 2.

(** [zlib.h:196-206]. *)
Definition Z_BINARY  : Z := 0.
Definition Z_TEXT    : Z := 1.
Definition Z_UNKNOWN : Z := 2.
Definition Z_FILTERED : Z := 1.
Definition Z_FIXED    : Z := 4.

(** [zutil.h:43]: [typedef unsigned long ulg], 64 bits on riscv64 LP64.
    [Base.v] stops at [u32] because [inftrees.c] has no 64-bit state;
    [opt_len]/[static_len] need this one. *)
Definition u64 (v : Z) : Z := v mod 18446744073709551616.

Lemma u64_id : forall v, 0 <= v < 18446744073709551616 -> u64 v = v.
Proof. intros; unfold u64; now apply Z.mod_small. Qed.

(** ** 2. The static tables ([trees.h], generated with [-DGEN_TREES_H])

    Transcribed verbatim from the vendored [trees.h] by
    [wp4work/wp4d/gen_tables.py]; [tr_static_init] would recompute them at
    run time only in the [!STDC] build, which this is not. *)
Definition static_ltree_code : list Z := [
  12;140;76;204;44;172;108;236;28;156;92;220;60;188;124;252;2;130;66;194;34;
  162;98;226;18;146;82;210;50;178;114;242;10;138;74;202;42;170;106;234;26;
  154;90;218;58;186;122;250;6;134;70;198;38;166;102;230;22;150;86;214;54;
  182;118;246;14;142;78;206;46;174;110;238;30;158;94;222;62;190;126;254;1;
  129;65;193;33;161;97;225;17;145;81;209;49;177;113;241;9;137;73;201;41;169;
  105;233;25;153;89;217;57;185;121;249;5;133;69;197;37;165;101;229;21;149;
  85;213;53;181;117;245;13;141;77;205;45;173;109;237;29;157;93;221;61;189;
  125;253;19;275;147;403;83;339;211;467;51;307;179;435;115;371;243;499;11;
  267;139;395;75;331;203;459;43;299;171;427;107;363;235;491;27;283;155;411;
  91;347;219;475;59;315;187;443;123;379;251;507;7;263;135;391;71;327;199;
  455;39;295;167;423;103;359;231;487;23;279;151;407;87;343;215;471;55;311;
  183;439;119;375;247;503;15;271;143;399;79;335;207;463;47;303;175;431;111;
  367;239;495;31;287;159;415;95;351;223;479;63;319;191;447;127;383;255;511;
  0;64;32;96;16;80;48;112;8;72;40;104;24;88;56;120;4;68;36;100;20;84;52;116;
  3;131;67;195;35;163;99;227].

Definition static_ltree_len : list Z := [
  8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;
  8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;
  8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;
  8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;9;9;9;9;
  9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;
  9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;
  9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;7;7;7;
  7;7;7;7;7;7;7;7;7;7;7;7;7;7;7;7;7;7;7;7;7;8;8;8;8;8;8;8;8].

Definition static_dtree_code : list Z := [
  0;16;8;24;4;20;12;28;2;18;10;26;6;22;14;30;1;17;9;25;5;21;13;29;3;19;11;
  27;7;23].

Definition static_dtree_len : list Z := [
  5;5;5;5;5;5;5;5;5;5;5;5;5;5;5;5;5;5;5;5;5;5;5;5;5;5;5;5;5;5].

Definition dist_code_l : list Z := [
  0;1;2;3;4;4;5;5;6;6;6;6;7;7;7;7;8;8;8;8;8;8;8;8;9;9;9;9;9;9;9;9;10;10;10;
  10;10;10;10;10;10;10;10;10;10;10;10;10;11;11;11;11;11;11;11;11;11;11;11;
  11;11;11;11;11;12;12;12;12;12;12;12;12;12;12;12;12;12;12;12;12;12;12;12;
  12;12;12;12;12;12;12;12;12;12;12;12;12;13;13;13;13;13;13;13;13;13;13;13;
  13;13;13;13;13;13;13;13;13;13;13;13;13;13;13;13;13;13;13;13;13;14;14;14;
  14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;
  14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;
  14;14;14;14;14;14;14;14;14;14;14;14;14;15;15;15;15;15;15;15;15;15;15;15;
  15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;
  15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;
  15;15;15;15;15;0;0;16;17;18;18;19;19;20;20;20;20;21;21;21;21;22;22;22;22;
  22;22;22;22;23;23;23;23;23;23;23;23;24;24;24;24;24;24;24;24;24;24;24;24;
  24;24;24;24;25;25;25;25;25;25;25;25;25;25;25;25;25;25;25;25;26;26;26;26;
  26;26;26;26;26;26;26;26;26;26;26;26;26;26;26;26;26;26;26;26;26;26;26;26;
  26;26;26;26;27;27;27;27;27;27;27;27;27;27;27;27;27;27;27;27;27;27;27;27;
  27;27;27;27;27;27;27;27;27;27;27;27;28;28;28;28;28;28;28;28;28;28;28;28;
  28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;
  28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;
  28;28;28;28;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;
  29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;
  29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29].

Definition length_code_l : list Z := [
  0;1;2;3;4;5;6;7;8;8;9;9;10;10;11;11;12;12;12;12;13;13;13;13;14;14;14;14;
  15;15;15;15;16;16;16;16;16;16;16;16;17;17;17;17;17;17;17;17;18;18;18;18;
  18;18;18;18;19;19;19;19;19;19;19;19;20;20;20;20;20;20;20;20;20;20;20;20;
  20;20;20;20;21;21;21;21;21;21;21;21;21;21;21;21;21;21;21;21;22;22;22;22;
  22;22;22;22;22;22;22;22;22;22;22;22;23;23;23;23;23;23;23;23;23;23;23;23;
  23;23;23;23;24;24;24;24;24;24;24;24;24;24;24;24;24;24;24;24;24;24;24;24;
  24;24;24;24;24;24;24;24;24;24;24;24;25;25;25;25;25;25;25;25;25;25;25;25;
  25;25;25;25;25;25;25;25;25;25;25;25;25;25;25;25;25;25;25;25;26;26;26;26;
  26;26;26;26;26;26;26;26;26;26;26;26;26;26;26;26;26;26;26;26;26;26;26;26;
  26;26;26;26;27;27;27;27;27;27;27;27;27;27;27;27;27;27;27;27;27;27;27;27;
  27;27;27;27;27;27;27;27;27;27;27;28].

Definition base_length_l : list Z := [
  0;1;2;3;4;5;6;7;8;10;12;14;16;20;24;28;32;40;48;56;64;80;96;112;128;160;
  192;224;0].

Definition base_dist_l : list Z := [
  0;1;2;3;4;6;8;12;16;24;32;48;64;96;128;192;256;384;512;768;1024;1536;2048;
  3072;4096;6144;8192;12288;16384;24576].

(** [trees.c:62-72]. *)
Definition extra_lbits_l : list Z :=
  [0;0;0;0;0;0;0;0;1;1;1;1;2;2;2;2;3;3;3;3;4;4;4;4;5;5;5;5;0].
Definition extra_lbits : zarr := zlist extra_lbits_l.
Definition extra_dbits_l : list Z :=
  [0;0;0;0;1;1;2;2;3;3;4;4;5;5;6;6;7;7;8;8;9;9;10;10;11;11;12;12;13;13].
Definition extra_dbits : zarr := zlist extra_dbits_l.
Definition extra_blbits_l : list Z :=
  [0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;2;3;7].
Definition extra_blbits : zarr := zlist extra_blbits_l.
Definition bl_order_l : list Z :=
  [16;17;18;0;8;7;9;6;10;5;11;4;12;3;13;2;14;1;15].
Definition bl_order : zarr := zlist bl_order_l.

(** ** 3. [ct_data] and the three dynamic trees

    [deflate.h:72-86]: a [ct_data] is two 16-bit slots, each a union.
    [tr_fc] is the [freq]/[code] slot, [tr_dl] the [dad]/[len] slot. *)

Record Tree : Type := mkTree { tr_fc : zarr ; tr_dl : zarr }.

Definition tzero : Tree := mkTree zzero zzero.

Definition t_freq (t : Tree) (i : Z) : Z := tr_fc t i.
(** ALIAS of [t_freq]: the same physical slot ([fc.code]). *)
Definition t_code (t : Tree) (i : Z) : Z := tr_fc t i.
Definition t_dad  (t : Tree) (i : Z) : Z := tr_dl t i.
(** ALIAS of [t_dad]: the same physical slot ([dl.len]). *)
Definition t_len  (t : Tree) (i : Z) : Z := tr_dl t i.

Definition t_setfreq (t : Tree) (i v : Z) : Tree :=
  mkTree (zset (tr_fc t) i (u16 v)) (tr_dl t).
Definition t_setcode (t : Tree) (i v : Z) : Tree :=
  mkTree (zset (tr_fc t) i (u16 v)) (tr_dl t).
Definition t_setdad (t : Tree) (i v : Z) : Tree :=
  mkTree (tr_fc t) (zset (tr_dl t) i (u16 v)).
Definition t_setlen (t : Tree) (i v : Z) : Tree :=
  mkTree (tr_fc t) (zset (tr_dl t) i (u16 v)).

Definition static_ltree : Tree := mkTree (zlist static_ltree_code) (zlist static_ltree_len).
Definition static_dtree : Tree := mkTree (zlist static_dtree_code) (zlist static_dtree_len).
Definition dist_code    : zarr := zlist dist_code_l.
Definition length_code  : zarr := zlist length_code_l.
Definition base_length  : zarr := zlist base_length_l.
Definition base_dist    : zarr := zlist base_dist_l.

(** [deflate.h:314-315].  [dist] is the match distance MINUS ONE. *)
Definition d_code (dist : Z) : Z :=
  if Z.ltb dist 256 then dist_code dist else dist_code (256 + Z.shiftr dist 7).

(** The three [tree_desc]s, identified by the index the R1 records call
    [tree_kind] (0 = [l_desc], 1 = [d_desc], 2 = [bl_desc]).
    [trees.c:131-138] gives the [static_tree_desc]s. *)
Definition TK_L  : Z := 0.
Definition TK_D  : Z := 1.
Definition TK_BL : Z := 2.

(** [static_bl_desc]'s [static_tree] is NULL ([trees.c:138]), which
    [gen_bitlen]/[build_tree] test for. *)
Definition sd_stree (k : Z) : option Tree :=
  if Z.eqb k TK_L then Some static_ltree
  else if Z.eqb k TK_D then Some static_dtree else None.
Definition sd_extra (k : Z) : zarr :=
  if Z.eqb k TK_L then extra_lbits
  else if Z.eqb k TK_D then extra_dbits else extra_blbits.
Definition sd_extra_base (k : Z) : Z := if Z.eqb k TK_L then LITERALS + 1 else 0.
Definition sd_elems (k : Z) : Z :=
  if Z.eqb k TK_L then L_CODES else if Z.eqb k TK_D then D_CODES else BL_CODES.
Definition sd_max_length (k : Z) : Z := if Z.eqb k TK_BL then MAX_BL_BITS else MAX_BITS.

(** ** 4. The [trees.c]-owned cluster of [deflate_state]

    [deflate.h:200-273].  [ts_bw] carries [bi_buf]/[bi_valid] AND the
    pending byte queue, because [put_byte] is the only way [trees.c]
    reaches [pending_buf].  [Deflate.v] wraps this cluster in the full
    [deflate_state]. *)

Record TSt : Type := mkTSt {
  ts_trees   : Z -> Tree;  (** [dyn_ltree] / [dyn_dtree] / [bl_tree] *)
  ts_maxcode : Z -> Z;     (** the three [desc->max_code] *)
  ts_blcount : zarr;       (** [bl_count[0..MAX_BITS]] *)
  ts_heap    : zarr;       (** [heap[0..2*L_CODES]] *)
  ts_heaplen : Z;
  ts_heapmax : Z;
  ts_depth   : zarr;       (** [depth[]], a [uch] array *)
  ts_symbuf  : zarr;       (** [sym_buf[]], a [uch] array *)
  ts_symnext : Z;
  ts_optlen  : Z;          (** [ulg] *)
  ts_statlen : Z;          (** [ulg] *)
  ts_matches : Z;
  ts_bw      : BW
}.
Definition set_trees (v : Z -> Tree) (s : TSt) : TSt :=
  mkTSt (v) (ts_maxcode s) (ts_blcount s) (ts_heap s) (ts_heaplen s) (ts_heapmax s) (ts_depth s) (ts_symbuf s) (ts_symnext s) (ts_optlen s) (ts_statlen s) (ts_matches s) (ts_bw s).
Definition set_maxcode (v : Z -> Z) (s : TSt) : TSt :=
  mkTSt (ts_trees s) (v) (ts_blcount s) (ts_heap s) (ts_heaplen s) (ts_heapmax s) (ts_depth s) (ts_symbuf s) (ts_symnext s) (ts_optlen s) (ts_statlen s) (ts_matches s) (ts_bw s).
Definition set_blcount (v : zarr) (s : TSt) : TSt :=
  mkTSt (ts_trees s) (ts_maxcode s) (v) (ts_heap s) (ts_heaplen s) (ts_heapmax s) (ts_depth s) (ts_symbuf s) (ts_symnext s) (ts_optlen s) (ts_statlen s) (ts_matches s) (ts_bw s).
Definition set_heap (v : zarr) (s : TSt) : TSt :=
  mkTSt (ts_trees s) (ts_maxcode s) (ts_blcount s) (v) (ts_heaplen s) (ts_heapmax s) (ts_depth s) (ts_symbuf s) (ts_symnext s) (ts_optlen s) (ts_statlen s) (ts_matches s) (ts_bw s).
Definition set_heaplen (v : Z) (s : TSt) : TSt :=
  mkTSt (ts_trees s) (ts_maxcode s) (ts_blcount s) (ts_heap s) (v) (ts_heapmax s) (ts_depth s) (ts_symbuf s) (ts_symnext s) (ts_optlen s) (ts_statlen s) (ts_matches s) (ts_bw s).
Definition set_heapmax (v : Z) (s : TSt) : TSt :=
  mkTSt (ts_trees s) (ts_maxcode s) (ts_blcount s) (ts_heap s) (ts_heaplen s) (v) (ts_depth s) (ts_symbuf s) (ts_symnext s) (ts_optlen s) (ts_statlen s) (ts_matches s) (ts_bw s).
Definition set_depth (v : zarr) (s : TSt) : TSt :=
  mkTSt (ts_trees s) (ts_maxcode s) (ts_blcount s) (ts_heap s) (ts_heaplen s) (ts_heapmax s) (v) (ts_symbuf s) (ts_symnext s) (ts_optlen s) (ts_statlen s) (ts_matches s) (ts_bw s).
Definition set_symbuf (v : zarr) (s : TSt) : TSt :=
  mkTSt (ts_trees s) (ts_maxcode s) (ts_blcount s) (ts_heap s) (ts_heaplen s) (ts_heapmax s) (ts_depth s) (v) (ts_symnext s) (ts_optlen s) (ts_statlen s) (ts_matches s) (ts_bw s).
Definition set_symnext (v : Z) (s : TSt) : TSt :=
  mkTSt (ts_trees s) (ts_maxcode s) (ts_blcount s) (ts_heap s) (ts_heaplen s) (ts_heapmax s) (ts_depth s) (ts_symbuf s) (v) (ts_optlen s) (ts_statlen s) (ts_matches s) (ts_bw s).
Definition set_optlen (v : Z) (s : TSt) : TSt :=
  mkTSt (ts_trees s) (ts_maxcode s) (ts_blcount s) (ts_heap s) (ts_heaplen s) (ts_heapmax s) (ts_depth s) (ts_symbuf s) (ts_symnext s) (v) (ts_statlen s) (ts_matches s) (ts_bw s).
Definition set_statlen (v : Z) (s : TSt) : TSt :=
  mkTSt (ts_trees s) (ts_maxcode s) (ts_blcount s) (ts_heap s) (ts_heaplen s) (ts_heapmax s) (ts_depth s) (ts_symbuf s) (ts_symnext s) (ts_optlen s) (v) (ts_matches s) (ts_bw s).
Definition set_matches (v : Z) (s : TSt) : TSt :=
  mkTSt (ts_trees s) (ts_maxcode s) (ts_blcount s) (ts_heap s) (ts_heaplen s) (ts_heapmax s) (ts_depth s) (ts_symbuf s) (ts_symnext s) (ts_optlen s) (ts_statlen s) (v) (ts_bw s).
Definition set_bw (v : BW) (s : TSt) : TSt :=
  mkTSt (ts_trees s) (ts_maxcode s) (ts_blcount s) (ts_heap s) (ts_heaplen s) (ts_heapmax s) (ts_depth s) (ts_symbuf s) (ts_symnext s) (ts_optlen s) (ts_statlen s) (ts_matches s) (v).

Definition set_tree (k : Z) (t : Tree) (s : TSt) : TSt :=
  set_trees (fun j => if Z.eqb j k then t else ts_trees s j) s.
Definition set_max (k v : Z) (s : TSt) : TSt :=
  set_maxcode (fun j => if Z.eqb j k then v else ts_maxcode s j) s.

(** ** 5. Small array helpers *)

(** [a[i .. i+n-1] := 0], the shape every [for (n = 0; n < K; n++) ... = 0]
    loop in [trees.c] has. *)
Fixpoint arr_zero (n : nat) (i : Z) (a : zarr) : zarr :=
  match n with
  | O => a
  | S k => arr_zero k (i + 1) (zset a i 0)
  end.

(** [tree[i .. i+n-1].Freq := 0]. *)
Fixpoint tree_zero_freq (n : nat) (i : Z) (t : Tree) : Tree :=
  match n with
  | O => t
  | S k => tree_zero_freq k (i + 1) (t_setfreq t i 0)
  end.

(** ** 6. [init_block] and [_tr_init] *)

(** [trees.c:439-450].  Note that only [0 .. L_CODES-1] of [dyn_ltree],
    [0 .. D_CODES-1] of [dyn_dtree] and [0 .. BL_CODES-1] of [bl_tree] are
    cleared: the internal-node slots above [elems] keep whatever the
    previous block left there.  Nothing reads them before writing them
    (argued in [tr_wf]), but the transcription clears exactly the C range. *)
Definition init_block (s : TSt) : TSt :=
  let l  := tree_zero_freq (Z.to_nat L_CODES)  0 (ts_trees s TK_L) in
  let d  := tree_zero_freq (Z.to_nat D_CODES)  0 (ts_trees s TK_D) in
  let b  := tree_zero_freq (Z.to_nat BL_CODES) 0 (ts_trees s TK_BL) in
  let l' := t_setfreq l END_BLOCK 1 in
  set_matches 0
    (set_symnext 0
      (set_statlen 0
        (set_optlen 0
          (set_tree TK_BL b (set_tree TK_D d (set_tree TK_L l' s)))))).

(** [trees.c:455-476].  [tr_static_init()] is a no-op in this build and the
    three [dyn_tree]/[stat_desc] pointer assignments are modelled by the
    fixed meaning of [TK_L]/[TK_D]/[TK_BL]. *)
Definition tr_init (s : TSt) : TSt :=
  init_block (set_bw {| bw_out := bw_out (ts_bw s); bw_buf := 0; bw_valid := 0 |} s).

(** ** 7. [pqdownheap] ([trees.c:497-526]) *)

(** [trees.c:497-499]: [smaller(tree, n, m, depth)]. *)
Definition smaller (t : Tree) (dep : zarr) (n m : Z) : bool :=
  (Z.ltb (t_freq t n) (t_freq t m))
  || ((Z.eqb (t_freq t n) (t_freq t m)) && (Z.leb (dep n) (dep m))).

(** One trip of [trees.c:510-524].  [v] is the value read once at [:508];
    [k] is the sift position.  Fuel: [k] at least doubles every trip and
    [heap_len < HEAP_SIZE = 573 < 2^10], so 12 is a static over-estimate.
    Fuel exhaustion falls through to the C's final [s->heap[k] = v]. *)
Fixpoint pq_down (fuel : nat) (t : Tree) (dep hp : zarr) (hlen v k : Z) : zarr :=
  match fuel with
  | O => zset hp k v
  | S f =>
      let j := 2 * k in
      if Z.leb j hlen then
        let j' := if (Z.ltb j hlen) && smaller t dep (hp (j + 1)) (hp j)
                  then j + 1 else j in
        if smaller t dep v (hp j') then zset hp k v
        else pq_down f t dep (zset hp k (hp j')) hlen v j'
      else zset hp k v
  end.

Definition pqdownheap (t : Tree) (dep hp : zarr) (hlen k : Z) : zarr :=
  pq_down 12%nat t dep hp hlen (hp k) k.

(** ** 8. [gen_bitlen] ([trees.c:538-611]) *)

(** [trees.c:559-574]: the descending walk over [heap[heap_max+1 .. HEAP_SIZE-1]].
    Carries [(tree, bl_count, opt_len, static_len, overflow)]. *)
Fixpoint gb_pass1 (fuel : nat) (k : Z) (hp : zarr) (maxc maxlen base : Z)
                  (extra : zarr) (stree : option Tree)
                  (h : Z) (t : Tree) (blc : zarr) (ol sl ov : Z)
  : Tree * zarr * Z * Z * Z :=
  match fuel with
  | O => (t, blc, ol, sl, ov)
  | S f =>
      if Z.leb HEAP_SIZE h then (t, blc, ol, sl, ov)
      else
        let n := hp h in
        let bits0 := t_len t (t_dad t n) + 1 in
        let bits := if Z.ltb maxlen bits0 then maxlen else bits0 in
        let ov' := if Z.ltb maxlen bits0 then ov + 1 else ov in
        let t1 := t_setlen t n bits in
        if Z.ltb maxc n then
          gb_pass1 f k hp maxc maxlen base extra stree (h + 1) t1 blc ol sl ov'
        else
          let blc1 := zset blc bits (u16 (blc bits + 1)) in
          let xbits := if Z.leb base n then extra (n - base) else 0 in
          let fq := t_freq t1 n in
          let ol1 := u64 (ol + fq * (bits + xbits)) in
          let sl1 := match stree with
                     | None => sl
                     | Some st => u64 (sl + fq * (t_len st n + xbits))
                     end in
          gb_pass1 f k hp maxc maxlen base extra stree (h + 1) t1 blc1 ol1 sl1 ov'
  end.

(** [trees.c:583]: [while (s->bl_count[bits] == 0) bits--].  Fuel
    [MAX_BITS+1]; the loop is guaranteed to stop because an overflow
    implies some shorter length is populated. *)
Fixpoint gb_findbits (fuel : nat) (blc : zarr) (bits : Z) : Z :=
  match fuel with
  | O => bits
  | S f => if Z.eqb (blc bits) 0 then gb_findbits f blc (bits - 1) else bits
  end.

(** [trees.c:581-591]: the overflow-adjust [do..while].  MEASURE:
    [overflow], strictly decreasing by 2 each trip, so the fuel is
    [overflow] itself. *)
Fixpoint gb_adjust (fuel : nat) (maxlen : Z) (blc : zarr) (ov : Z) : zarr :=
  match fuel with
  | O => blc
  | S f =>
      let bits := gb_findbits (Z.to_nat MAX_BITS + 1) blc (maxlen - 1) in
      let blc1 := zset blc bits (u16 (blc bits - 1)) in
      let blc2 := zset blc1 (bits + 1) (u16 (blc1 (bits + 1) + 2)) in
      let blc3 := zset blc2 maxlen (u16 (blc2 maxlen - 1)) in
      if Z.ltb 2 ov then gb_adjust f maxlen blc3 (ov - 2) else blc3
  end.

(** [trees.c:598-610]: the recompute pass, as ONE fuelled loop over the
    pair [(bits, n)] plus the shared descending [h].

    BUG-FOR-BUG: [if (m > max_code) continue;] at [:602] continues the
    INNER [while (n != 0)] loop, so it does NOT decrement [n] — it only
    consumes one more [heap] entry.  A model that decrements [n] there
    produces different lengths whenever the heap holds internal nodes
    between leaves, which it always does. *)
Fixpoint gb_pass2 (fuel : nat) (hp : zarr) (maxc : Z)
                  (t : Tree) (blc : zarr) (bits n h ol : Z) : Tree * Z :=
  match fuel with
  | O => (t, ol)
  | S f =>
      if Z.eqb n 0 then
        (if Z.leb bits 1 then (t, ol)
         else gb_pass2 f hp maxc t blc (bits - 1) (blc (bits - 1)) h ol)
      else
        let h' := h - 1 in
        let m := hp h' in
        if Z.ltb maxc m then gb_pass2 f hp maxc t blc bits n h' ol
        else if Z.eqb (t_len t m) bits then
          gb_pass2 f hp maxc t blc bits (n - 1) h' ol
        else
          let ol' := u64 (ol + (bits - t_len t m) * t_freq t m) in
          gb_pass2 f hp maxc (t_setlen t m bits) blc bits (n - 1) h' ol'
  end.

(** [gen_bitlen] on tree kind [k]. *)
Definition gen_bitlen (k : Z) (s : TSt) : TSt :=
  let t0     := ts_trees s k in
  let maxc   := ts_maxcode s k in
  let stree  := sd_stree k in
  let extra  := sd_extra k in
  let base   := sd_extra_base k in
  let maxlen := sd_max_length k in
  (* :552 *)
  let blc0 := arr_zero (Z.to_nat MAX_BITS + 1) 0 (ts_blcount s) in
  (* :557 *)
  let t1 := t_setlen t0 (ts_heap s (ts_heapmax s)) 0 in
  (* :559-574 *)
  let r := gb_pass1 (Z.to_nat HEAP_SIZE + 1) k (ts_heap s) maxc maxlen base extra
                    stree (ts_heapmax s + 1) t1 blc0
                    (ts_optlen s) (ts_statlen s) 0 in
  match r with
  | (t2, blc1, ol1, sl1, ov) =>
      if Z.eqb ov 0 then
        set_statlen sl1 (set_optlen ol1 (set_blcount blc1 (set_tree k t2 s)))
      else
        (* :581-591 *)
        let blc2 := gb_adjust (Z.to_nat ov + 1) maxlen blc1 ov in
        (* :598-610; h is still HEAP_SIZE *)
        let r2 := gb_pass2 (2 * Z.to_nat HEAP_SIZE + Z.to_nat MAX_BITS + 4)
                           (ts_heap s) maxc t2 blc2 maxlen (blc2 maxlen)
                           HEAP_SIZE ol1 in
        match r2 with
        | (t3, ol2) =>
            set_statlen sl1 (set_optlen ol2 (set_blcount blc2 (set_tree k t3 s)))
        end
  end.

(** ** 9. [gen_codes] ([trees.c:154-161] and [:202-231]) *)

(** [trees.c:154-161] [bi_reverse].  A [do..while], so it runs
    [max 1 len] times even for [len <= 0]. *)
Fixpoint bi_rev_go (n : nat) (code res : Z) : Z :=
  match n with
  | O => res
  | S k => bi_rev_go k (Z.shiftr code 1) (u32 (Z.shiftl (Z.lor res (Z.land code 1)) 1))
  end.

Definition bi_reverse (code len : Z) : Z :=
  Z.shiftr (bi_rev_go (Z.to_nat (Z.max 1 len)) code 0) 1.

(** [trees.c:211-214]: [code = (code + bl_count[bits-1]) << 1] in an
    [unsigned], then [next_code[bits] = (ush)code]. *)
Fixpoint gc_next (fuel : nat) (bits code : Z) (blc nc : zarr) : zarr :=
  match fuel with
  | O => nc
  | S f =>
      let code' := u32 (Z.shiftl (code + blc (bits - 1)) 1) in
      gc_next f (bits + 1) code' blc (zset nc bits (u16 code'))
  end.

(** [trees.c:222-230]: assign the reversed codes, [next_code[len]++]. *)
Fixpoint gc_assign (fuel : nat) (n maxc : Z) (t : Tree) (nc : zarr) : Tree :=
  match fuel with
  | O => t
  | S f =>
      if Z.ltb maxc n then t
      else
        let len := t_len t n in
        if Z.eqb len 0 then gc_assign f (n + 1) maxc t nc
        else
          let t' := t_setcode t n (bi_reverse (nc len) len) in
          gc_assign f (n + 1) maxc t' (zset nc len (u16 (nc len + 1)))
  end.

Definition gen_codes (t : Tree) (maxc : Z) (blc : zarr) : Tree :=
  let nc := gc_next (Z.to_nat MAX_BITS) 1 0 blc zzero in
  gc_assign (Z.to_nat L_CODES + 3) 0 maxc t nc.

(** ** 10. [build_tree] ([trees.c:625-704]) *)

(** [trees.c:639-646]: the initial heap.  Returns the updated tree, heap,
    depth, heap_len and max_code. *)
Fixpoint bt_init (fuel : nat) (n elems : Z) (t : Tree) (hp dep : zarr)
                 (hlen maxc : Z) : Tree * zarr * zarr * Z * Z :=
  match fuel with
  | O => (t, hp, dep, hlen, maxc)
  | S f =>
      if Z.leb elems n then (t, hp, dep, hlen, maxc)
      else if Z.eqb (t_freq t n) 0 then
        bt_init f (n + 1) elems (t_setlen t n 0) hp dep hlen maxc
      else
        bt_init f (n + 1) elems t (zset hp (hlen + 1) n) (zset dep n 0) (hlen + 1) n
  end.

(** [trees.c:653-659]: force at least two codes of non-zero frequency.
    [++max_code] mutates [max_code]; [s->opt_len--] and
    [s->static_len -= stree[node].Len] are [ulg] arithmetic and WRAP when
    the counters are 0, which they are for a block whose only symbol is
    [END_BLOCK]. *)
Fixpoint bt_force2 (fuel : nat) (stree : option Tree) (t : Tree) (hp dep : zarr)
                   (hlen maxc ol sl : Z) : Tree * zarr * zarr * Z * Z * Z * Z :=
  match fuel with
  | O => (t, hp, dep, hlen, maxc, ol, sl)
  | S f =>
      if Z.leb 2 hlen then (t, hp, dep, hlen, maxc, ol, sl)
      else
        let maxc' := if Z.ltb maxc 2 then maxc + 1 else maxc in
        let node  := if Z.ltb maxc 2 then maxc + 1 else 0 in
        let hlen' := hlen + 1 in
        let hp'   := zset hp hlen' node in
        let t'    := t_setfreq t node 1 in
        let dep'  := zset dep node 0 in
        let ol'   := u64 (ol - 1) in
        let sl'   := match stree with
                     | None => sl
                     | Some st => u64 (sl - t_len st node)
                     end in
        bt_force2 f stree t' hp' dep' hlen' maxc' ol' sl'
  end.

(** [trees.c:665]: [for (n = s->heap_len/2; n >= 1; n--) pqdownheap(s, tree, n)]. *)
Fixpoint bt_heapify (fuel : nat) (t : Tree) (dep hp : zarr) (hlen n : Z) : zarr :=
  match fuel with
  | O => hp
  | S f =>
      if Z.ltb n 1 then hp
      else bt_heapify f t dep (pqdownheap t dep hp hlen n) hlen (n - 1)
  end.

(** The loop-carried state of the combine loop ([trees.c:671-693]).
    Named so a machine-level walk can index its invariant by trip count. *)
Record BtSt : Type := mkBtSt {
  b_tree : Tree;
  b_heap : zarr;
  b_dep  : zarr;
  b_hlen : Z;
  b_hmax : Z;
  b_node : Z
}.

Inductive BtStep : Type :=
| BtCont (st : BtSt)   (** [heap_len >= 2], go round again *)
| BtDone (st : BtSt).  (** the [while] condition failed *)

(** ONE trip of [trees.c:671-693], including the [pqremove] macro
    ([trees.c:486-491]). *)
Definition bt_step (st : BtSt) : BtStep :=
  (* pqremove: n = heap[1]; heap[1] = heap[heap_len--]; pqdownheap(1) *)
  let n     := b_heap st SMALLEST in
  let hp1   := zset (b_heap st) SMALLEST (b_heap st (b_hlen st)) in
  let hlen1 := b_hlen st - 1 in
  let hp2   := pqdownheap (b_tree st) (b_dep st) hp1 hlen1 SMALLEST in
  let m     := hp2 SMALLEST in
  (* :675-676 *)
  let hmax1 := b_hmax st - 1 in
  let hp3   := zset hp2 hmax1 n in
  let hmax2 := hmax1 - 1 in
  let hp4   := zset hp3 hmax2 m in
  (* :679-682 *)
  let node  := b_node st in
  let t1    := t_setfreq (b_tree st) node (t_freq (b_tree st) n + t_freq (b_tree st) m) in
  let dep1  := zset (b_dep st) node
                    (u8 ((if Z.leb (b_dep st m) (b_dep st n)
                          then b_dep st n else b_dep st m) + 1)) in
  let t2    := t_setdad (t_setdad t1 m node) n node in
  (* :690-691 *)
  let hp5   := zset hp4 SMALLEST node in
  let hp6   := pqdownheap t2 dep1 hp5 hlen1 SMALLEST in
  let st'   := {| b_tree := t2; b_heap := hp6; b_dep := dep1;
                  b_hlen := hlen1; b_hmax := hmax2; b_node := node + 1 |} in
  if Z.leb 2 hlen1 then BtCont st' else BtDone st'.

(** The state after [j] fall-through trips — the term a machine-level
    combine-loop invariant is indexed by. *)
Fixpoint bt_iter (j : nat) (st : BtSt) : option BtSt :=
  match j with
  | O => Some st
  | S j' => match bt_step st with
            | BtCont st' => bt_iter j' st'
            | BtDone _ => None
            end
  end.

Fixpoint bt_loop (fuel : nat) (st : BtSt) : option BtSt :=
  match fuel with
  | O => None
  | S f => match bt_step st with
           | BtCont st' => bt_loop f st'
           | BtDone st' => Some st'
           end
  end.

(** [build_tree] on tree kind [k]. *)
Definition build_tree (k : Z) (s : TSt) : TSt :=
  let elems := sd_elems k in
  let stree := sd_stree k in
  (* :637-646 *)
  match bt_init (Z.to_nat L_CODES + 2) 0 elems (ts_trees s k) (ts_heap s)
                (ts_depth s) 0 (-1) with
  | (t0, hp0, dep0, hlen0, maxc0) =>
      (* :653-659 *)
      match bt_force2 3%nat stree t0 hp0 dep0 hlen0 maxc0
                      (ts_optlen s) (ts_statlen s) with
      | (t1, hp1, dep1, hlen1, maxc1, ol1, sl1) =>
          (* :665 *)
          let hp2 := bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1 (hlen1 / 2) in
          (* :670-693 *)
          let st0 := {| b_tree := t1; b_heap := hp2; b_dep := dep1;
                        b_hlen := hlen1; b_hmax := HEAP_SIZE; b_node := elems |} in
          match bt_loop (Z.to_nat HEAP_SIZE) st0 with
          | None => s   (* unreachable: the fuel is a static over-estimate *)
          | Some stf =>
              (* :695 *)
              let hmax := b_hmax stf - 1 in
              let hp3  := zset (b_heap stf) hmax (b_heap stf SMALLEST) in
              let s1   := set_statlen sl1 (set_optlen ol1
                            (set_heapmax hmax (set_heaplen (b_hlen stf)
                              (set_depth (b_dep stf)
                                (set_heap hp3
                                  (set_max k maxc1 (set_tree k (b_tree stf) s))))))) in
              (* :700 *)
              let s2 := gen_bitlen k s1 in
              (* :703 *)
              set_tree k (gen_codes (ts_trees s2 k) maxc1 (ts_blcount s2)) s2
          end
      end
  end.

(** ** 11. [scan_tree] / [send_tree] ([trees.c:710-792])

    The two share their control flow exactly; only the action differs
    (bump a [bl_tree] frequency vs emit through the bit writer).  They are
    transcribed separately, line for line, rather than factored, so that a
    reader can check each against its own C. *)

Fixpoint scan_go (fuel : nat) (t : Tree) (maxc n prevlen nextlen count maxcnt mincnt : Z)
                 (bl : Tree) : Tree :=
  match fuel with
  | O => bl
  | S f =>
      if Z.ltb maxc n then bl
      else
        let curlen  := nextlen in
        let nextlen' := t_len t (n + 1) in
        let count'  := count + 1 in
        if (Z.ltb count' maxcnt) && (Z.eqb curlen nextlen') then
          scan_go f t maxc (n + 1) prevlen nextlen' count' maxcnt mincnt bl
        else
          let bl' :=
            if Z.ltb count' mincnt then t_setfreq bl curlen (t_freq bl curlen + count')
            else if negb (Z.eqb curlen 0) then
              let b1 := if negb (Z.eqb curlen prevlen)
                        then t_setfreq bl curlen (t_freq bl curlen + 1) else bl in
              t_setfreq b1 REP_3_6 (t_freq b1 REP_3_6 + 1)
            else if Z.leb count' 10 then
              t_setfreq bl REPZ_3_10 (t_freq bl REPZ_3_10 + 1)
            else t_setfreq bl REPZ_11_138 (t_freq bl REPZ_11_138 + 1) in
          let mc := if Z.eqb nextlen' 0 then 138
                    else if Z.eqb curlen nextlen' then 6 else 7 in
          let mn := if Z.eqb nextlen' 0 then 3
                    else if Z.eqb curlen nextlen' then 3 else 4 in
          scan_go f t maxc (n + 1) curlen nextlen' 0 mc mn bl'
  end.

(** [trees.c:710-745].  Writes the [0xffff] guard at [tree[max_code+1]]
    ([:720]) and returns BOTH the guarded tree and the updated [bl_tree] —
    the guard is a real store the next [send_tree] reads. *)
Definition scan_tree (t : Tree) (maxc : Z) (bl : Tree) : Tree * Tree :=
  let nextlen := t_len t 0 in
  let mc := if Z.eqb nextlen 0 then 138 else 7 in
  let mn := if Z.eqb nextlen 0 then 3 else 4 in
  let tg := t_setlen t (maxc + 1) 65535 in
  (tg, scan_go (Z.to_nat L_CODES + 3) tg maxc 0 (-1) nextlen 0 mc mn bl).

(** [trees.c:238]: [send_code(s, c, tree)]. *)
Definition send_code (c : Z) (t : Tree) (b : BW) : BW :=
  bw_send_bits (t_code t c) (t_len t c) b.

(** [trees.c:768]: [do { send_code(curlen); } while (--count != 0)]. *)
Fixpoint send_rep (fuel : nat) (c : Z) (bl : Tree) (count : Z) (b : BW) : BW :=
  match fuel with
  | O => b
  | S f =>
      let b' := send_code c bl b in
      if Z.eqb (count - 1) 0 then b' else send_rep f c bl (count - 1) b'
  end.

Fixpoint send_go (fuel : nat) (t : Tree) (maxc n prevlen nextlen count maxcnt mincnt : Z)
                 (bl : Tree) (b : BW) : BW :=
  match fuel with
  | O => b
  | S f =>
      if Z.ltb maxc n then b
      else
        let curlen   := nextlen in
        let nextlen' := t_len t (n + 1) in
        let count'   := count + 1 in
        if (Z.ltb count' maxcnt) && (Z.eqb curlen nextlen') then
          send_go f t maxc (n + 1) prevlen nextlen' count' maxcnt mincnt bl b
        else
          let b' :=
            if Z.ltb count' mincnt then send_rep 140%nat curlen bl count' b
            else if negb (Z.eqb curlen 0) then
              let p := if negb (Z.eqb curlen prevlen)
                       then (send_code curlen bl b, count' - 1) else (b, count') in
              let b1 := fst p in let c1 := snd p in
              bw_send_bits (c1 - 3) 2 (send_code REP_3_6 bl b1)
            else if Z.leb count' 10 then
              bw_send_bits (count' - 3) 3 (send_code REPZ_3_10 bl b)
            else
              bw_send_bits (count' - 11) 7 (send_code REPZ_11_138 bl b) in
          let mc := if Z.eqb nextlen' 0 then 138
                    else if Z.eqb curlen nextlen' then 6 else 7 in
          let mn := if Z.eqb nextlen' 0 then 3
                    else if Z.eqb curlen nextlen' then 3 else 4 in
          send_go f t maxc (n + 1) curlen nextlen' 0 mc mn bl b'
  end.

(** [trees.c:751-792].  The guard at [tree[max_code+1]] is "already set" by
    the preceding [scan_tree] ([:760]). *)
Definition send_tree (t : Tree) (maxc : Z) (bl : Tree) (b : BW) : BW :=
  let nextlen := t_len t 0 in
  let mc := if Z.eqb nextlen 0 then 138 else 7 in
  let mn := if Z.eqb nextlen 0 then 3 else 4 in
  send_go (Z.to_nat L_CODES + 3) t maxc 0 (-1) nextlen 0 mc mn bl b.

(** ** 12. [build_bl_tree] ([trees.c:798-824]) *)

(** [trees.c:815-817]: [for (i = BL_CODES-1; i >= 3; i--) if (...Len != 0) break]. *)
Fixpoint bbl_scan (fuel : nat) (bl : Tree) (i : Z) : Z :=
  match fuel with
  | O => i
  | S f =>
      if Z.ltb i 3 then i
      else if negb (Z.eqb (t_len bl (bl_order i)) 0) then i
      else bbl_scan f bl (i - 1)
  end.

Definition build_bl_tree (s : TSt) : Z * TSt :=
  (* :802-803 *)
  let p1 := scan_tree (ts_trees s TK_L) (ts_maxcode s TK_L) (ts_trees s TK_BL) in
  let s1 := set_tree TK_BL (snd p1) (set_tree TK_L (fst p1) s) in
  let p2 := scan_tree (ts_trees s1 TK_D) (ts_maxcode s1 TK_D) (ts_trees s1 TK_BL) in
  let s2 := set_tree TK_BL (snd p2) (set_tree TK_D (fst p2) s1) in
  (* :806 *)
  let s3 := build_tree TK_BL s2 in
  (* :815-819 *)
  let mbi := bbl_scan (Z.to_nat BL_CODES + 1) (ts_trees s3 TK_BL) (BL_CODES - 1) in
  (mbi, set_optlen (u64 (ts_optlen s3 + 3 * (mbi + 1) + 5 + 5 + 4)) s3).

(** ** 13. [send_all_trees] ([trees.c:831-853]) *)

Fixpoint sat_ranks (fuel : nat) (rank blcodes : Z) (bl : Tree) (b : BW) : BW :=
  match fuel with
  | O => b
  | S f =>
      if Z.leb blcodes rank then b
      else sat_ranks f (rank + 1) blcodes bl
                     (bw_send_bits (t_len bl (bl_order rank)) 3 b)
  end.

Definition send_all_trees (lcodes dcodes blcodes : Z) (s : TSt) : BW :=
  let b0 := bw_send_bits (lcodes - 257) 5 (ts_bw s) in
  let b1 := bw_send_bits (dcodes - 1) 5 b0 in
  let b2 := bw_send_bits (blcodes - 4) 4 b1 in
  let b3 := sat_ranks (Z.to_nat BL_CODES + 1) 0 blcodes (ts_trees s TK_BL) b2 in
  let b4 := send_tree (ts_trees s TK_L) (lcodes - 1) (ts_trees s TK_BL) b3 in
  send_tree (ts_trees s TK_D) (dcodes - 1) (ts_trees s TK_BL) b4.

(** ** 14. [compress_block] ([trees.c:898-949])

    A walk indexes its emit-loop invariant by symbol count, so this gets
    the [_step] / [_iter] treatment. *)

Record CbSt : Type := mkCbSt { c_sx : Z ; c_bw : BW }.

Inductive CbStep : Type := CbCont (st : CbSt) | CbDone (st : CbSt).

(** ONE symbol of [trees.c:906-946]. *)
Definition cb_step (sym : zarr) (symnext : Z) (lt dt : Tree) (st : CbSt) : CbStep :=
  let sx   := c_sx st in
  let dist := Z.land (sym sx) 255 + Z.shiftl (Z.land (sym (sx + 1)) 255) 8 in
  let lc   := sym (sx + 2) in
  let sx'  := sx + 3 in
  let b' :=
    if Z.eqb dist 0 then send_code lc lt (c_bw st)
    else
      let code := length_code lc in
      let b1   := send_code (code + LITERALS + 1) lt (c_bw st) in
      let ex   := extra_lbits code in
      let b2   := if Z.eqb ex 0 then b1
                  else bw_send_bits (lc - base_length code) ex b1 in
      let d1   := dist - 1 in
      let dc   := d_code d1 in
      let b3   := send_code dc dt b2 in
      let ex2  := extra_dbits dc in
      if Z.eqb ex2 0 then b3 else bw_send_bits (d1 - base_dist dc) ex2 b3 in
  let st' := {| c_sx := sx'; c_bw := b' |} in
  if Z.ltb sx' symnext then CbCont st' else CbDone st'.

Fixpoint cb_iter (j : nat) (sym : zarr) (symnext : Z) (lt dt : Tree) (st : CbSt)
  : option CbSt :=
  match j with
  | O => Some st
  | S j' => match cb_step sym symnext lt dt st with
            | CbCont st' => cb_iter j' sym symnext lt dt st'
            | CbDone _ => None
            end
  end.

Fixpoint cb_loop (fuel : nat) (sym : zarr) (symnext : Z) (lt dt : Tree) (st : CbSt)
  : option CbSt :=
  match fuel with
  | O => None
  | S f => match cb_step sym symnext lt dt st with
           | CbCont st' => cb_loop f sym symnext lt dt st'
           | CbDone st' => Some st'
           end
  end.

Definition compress_block (sym : zarr) (symnext : Z) (lt dt : Tree) (b : BW) : BW :=
  let b' :=
    if Z.eqb symnext 0 then b
    else match cb_loop (Z.to_nat symnext + 1) sym symnext lt dt
                       {| c_sx := 0; c_bw := b |} with
         | None => b   (* unreachable: fuel is a static over-estimate *)
         | Some st => c_bw st
         end in
  send_code END_BLOCK lt b'.

(** ** 15. [detect_data_type] ([trees.c:964-989]) *)

Fixpoint ddt_block (fuel : nat) (lt : Tree) (n mask : Z) : bool :=
  match fuel with
  | O => false
  | S f =>
      if Z.ltb 31 n then false
      else if (Z.eqb (Z.land mask 1) 1) && negb (Z.eqb (t_freq lt n) 0) then true
      else ddt_block f lt (n + 1) (Z.shiftr mask 1)
  end.

Fixpoint ddt_allow (fuel : nat) (lt : Tree) (n : Z) : bool :=
  match fuel with
  | O => false
  | S f =>
      if Z.leb LITERALS n then false
      else if negb (Z.eqb (t_freq lt n) 0) then true
      else ddt_allow f lt (n + 1)
  end.

Definition detect_data_type (lt : Tree) : Z :=
  if ddt_block 33%nat lt 0 4093624447 (* 0xf3ffc07f *) then Z_BINARY
  else if negb (Z.eqb (t_freq lt 9) 0) then Z_TEXT
  else if negb (Z.eqb (t_freq lt 10) 0) then Z_TEXT
  else if negb (Z.eqb (t_freq lt 13) 0) then Z_TEXT
  else if ddt_allow (Z.to_nat LITERALS + 1) lt 32 then Z_TEXT
  else Z_BINARY.

(** ** 16. [_tr_tally], [_tr_stored_block], [_tr_align] *)

(** [trees.c:1093-1117] (equivalently the [_tr_tally_lit]/[_tr_tally_dist]
    macros at [deflate.h:351-369], which the non-debug build inlines and
    which are byte-for-byte the same computation).  Returns the flush flag
    [sym_next == sym_end] alongside the new state. *)
Definition tr_tally (dist lc sym_end : Z) (s : TSt) : bool * TSt :=
  let sn  := ts_symnext s in
  let sb1 := zset (ts_symbuf s) sn (u8 dist) in
  let sb2 := zset sb1 (sn + 1) (u8 (Z.shiftr dist 8)) in
  let sb3 := zset sb2 (sn + 2) (u8 lc) in
  let sn' := sn + 3 in
  let s1  := set_symnext sn' (set_symbuf sb3 s) in
  let s2 :=
    if Z.eqb dist 0 then
      set_tree TK_L (t_setfreq (ts_trees s1 TK_L) lc (t_freq (ts_trees s1 TK_L) lc + 1)) s1
    else
      let d1 := dist - 1 in
      let lt := ts_trees s1 TK_L in
      let li := length_code lc + LITERALS + 1 in
      let lt' := t_setfreq lt li (t_freq lt li + 1) in
      let dt := ts_trees s1 TK_D in
      let di := d_code d1 in
      let dt' := t_setfreq dt di (t_freq dt di + 1) in
      set_matches (ts_matches s1 + 1)
        (set_tree TK_D dt' (set_tree TK_L lt' s1)) in
  (Z.eqb sn' sym_end, s2).

(** [trees.c:858-873].  [dat] is the [stored_len] bytes at [buf]; the C
    skips the [zmemcpy] when [stored_len == 0] but adds [stored_len] to
    [pending] unconditionally, which is the same thing.
    [(ush)~stored_len] is a 64-bit complement truncated to 16 bits. *)
Definition tr_stored_block (dat : list Z) (stored_len last : Z) (s : TSt) : TSt :=
  let b0 := bw_send_bits (Z.shiftl STORED_BLOCK 1 + last) 3 (ts_bw s) in
  let b1 := bw_windup b0 in
  let b2 := bw_put_short stored_len b1 in
  let b3 := bw_put_short (u16 (-stored_len - 1)) b2 in
  let b4 := {| bw_out := bw_out b3 ++ map u8 dat;
               bw_buf := bw_buf b3; bw_valid := bw_valid b3 |} in
  set_bw b4 s.

(** [trees.c:886-893]. *)
Definition tr_align (s : TSt) : TSt :=
  let b0 := bw_send_bits (Z.shiftl STATIC_TREES 1) 3 (ts_bw s) in
  let b1 := send_code END_BLOCK static_ltree b0 in
  set_bw (bw_flush b1) s.

(** [trees.c:878-880]. *)
Definition tr_flush_bits (s : TSt) : TSt := set_bw (bw_flush (ts_bw s)) s.

(** ** 17. [_tr_flush_block] ([trees.c:995-1087])

    [buf] is [None] for the C's [Z_NULL] (which [deflate_slow]'s
    [FLUSH_BLOCK_ONLY] passes when [block_start < 0]) and [Some dat] for a
    live window pointer, [dat] being the [stored_len] bytes there.

    QUARANTINED HEURISTIC ([:1025-1045]): the stored / static / dynamic
    choice.  Transcribed exactly because the refinement proof needs it;
    the round-trip theorem does not depend on which arm is taken. *)
Definition tr_flush_block (buf : option (list Z)) (stored_len last level strategy dtype : Z)
                          (s : TSt) : Z * TSt :=
  if Z.ltb 0 level then
    (* :1004-1005 *)
    let dtype' := if Z.eqb dtype Z_UNKNOWN
                  then detect_data_type (ts_trees s TK_L) else dtype in
    (* :1008-1012 *)
    let s1 := build_tree TK_D (build_tree TK_L s) in
    (* :1022 *)
    let p  := build_bl_tree s1 in
    let mbi := fst p in let s2 := snd p in
    (* :1025-1035 *)
    let static_lenb := u64 (ts_statlen s2 + 3 + 7) / 8 in
    let opt_lenb0   := u64 (ts_optlen s2 + 3 + 7) / 8 in
    let opt_lenb    := if (Z.leb static_lenb opt_lenb0) || (Z.eqb strategy Z_FIXED)
                       then static_lenb else opt_lenb0 in
    (* :1045-1072 *)
    let s3 :=
      match buf with
      | Some dat =>
          if Z.leb (stored_len + 4) opt_lenb
          then Some (tr_stored_block dat stored_len last s2) else None
      | None => None
      end in
    let s4 :=
      match s3 with
      | Some sx => sx
      | None =>
          if Z.eqb static_lenb opt_lenb then
            let b0 := bw_send_bits (Z.shiftl STATIC_TREES 1 + last) 3 (ts_bw s2) in
            set_bw (compress_block (ts_symbuf s2) (ts_symnext s2)
                                   static_ltree static_dtree b0) s2
          else
            let b0 := bw_send_bits (Z.shiftl DYN_TREES 1 + last) 3 (ts_bw s2) in
            let b1 := send_all_trees (ts_maxcode s2 TK_L + 1) (ts_maxcode s2 TK_D + 1)
                                     (mbi + 1) (set_bw b0 s2) in
            set_bw (compress_block (ts_symbuf s2) (ts_symnext s2)
                                   (ts_trees s2 TK_L) (ts_trees s2 TK_D) b1) s2
      end in
    (* :1077-1084 *)
    let s5 := init_block s4 in
    (dtype', if Z.eqb last 0 then s5 else set_bw (bw_windup (ts_bw s5)) s5)
  else
    (* :1038-1039: level == 0 forces a stored block *)
    let opt_lenb := stored_len + 5 in
    let s4 :=
      match buf with
      | Some dat =>
          if Z.leb (stored_len + 4) opt_lenb
          then tr_stored_block dat stored_len last s
          else s   (* unreachable: stored_len+4 <= stored_len+5 always *)
      | None =>
          (* [Assert(buf != 0, "lost buf")] at :1038; the C would then take
             the [static_lenb == opt_lenb] arm.  Kept for totality. *)
          let b0 := bw_send_bits (Z.shiftl STATIC_TREES 1 + last) 3 (ts_bw s) in
          set_bw (compress_block (ts_symbuf s) (ts_symnext s)
                                 static_ltree static_dtree b0) s
      end in
    let s5 := init_block s4 in
    (dtype, if Z.eqb last 0 then s5 else set_bw (bw_windup (ts_bw s5)) s5).

(** ** 18. The inline tally macros — what [deflate.c] actually calls

    [deflate.h:351-369].  With [ZLIB_DEBUG] off, [deflate_slow] /
    [deflate_fast] / [deflate_rle] / [deflate_huff] use these MACROS, not
    the function [_tr_tally] above.

    BUG-FOR-BUG, and it shows up in the records: the macros do NOT
    increment [s->matches].  The function does ([trees.c:1106]).  So on
    this build [s->matches] stays 0 for the whole stream even when the
    block is all matches — which is what the [_tr_flush_block] R1 records
    from the delivered binary show ([out_matches = 0] on blocks with
    hundreds of symbols).  A model that used the function here would
    disagree, and would also mis-drive [deflate_stored]'s
    [s->matches < 2] hash-slide bookkeeping. *)

Definition tr_tally_lit (c sym_end : Z) (s : TSt) : bool * TSt :=
  let sn  := ts_symnext s in
  let cc  := u8 c in
  let sb  := zset (zset (zset (ts_symbuf s) sn 0) (sn + 1) 0) (sn + 2) cc in
  let sn' := sn + 3 in
  let lt  := ts_trees s TK_L in
  (Z.eqb sn' sym_end,
   set_tree TK_L (t_setfreq lt cc (t_freq lt cc + 1))
     (set_symnext sn' (set_symbuf sb s))).

Definition tr_tally_dist (distance length sym_end : Z) (s : TSt) : bool * TSt :=
  let len  := u8 length in
  let dist := u16 distance in
  let sn   := ts_symnext s in
  let sb   := zset (zset (zset (ts_symbuf s) sn (u8 dist))
                         (sn + 1) (u8 (Z.shiftr dist 8)))
                   (sn + 2) len in
  let sn'  := sn + 3 in
  let d1   := dist - 1 in
  let lt   := ts_trees s TK_L in
  let li   := length_code len + LITERALS + 1 in
  let lt'  := t_setfreq lt li (t_freq lt li + 1) in
  let dt   := ts_trees s TK_D in
  let di   := d_code d1 in
  let dt'  := t_setfreq dt di (t_freq dt di + 1) in
  (Z.eqb sn' sym_end,
   set_tree TK_D dt' (set_tree TK_L lt' (set_symnext sn' (set_symbuf sb s)))).

(** ** 19. The LZ77 token stream and the three round-trip contracts

    c5-invariants.md §2.2.  The matcher, the block-boundary choice and
    [_tr_flush_block]'s stored/static/dynamic comparison are QUARANTINED:
    the round-trip theorem is proved for ANY token stream satisfying
    [cEnc] / [cEmpty] / [cRes] and ANY block split.  These are the only
    facts the correctness core may assume about anything in this file or
    in [Deflate.v]. *)

Inductive Tok : Set :=
| TLit   (b : Z)          (** a literal byte *)
| TMatch (len dist : Z).  (** [len] bytes at distance [dist] *)

(** The tokens [compress_block] reads back out of [sym_buf], i.e. the
    decoding of the three-byte-per-symbol layout ([trees.c:911-914]).
    [len] is stored biased by [MIN_MATCH] and [dist] little-endian. *)
Fixpoint sym_toks (fuel : nat) (sym : zarr) (sx symnext : Z) : list Tok :=
  match fuel with
  | O => []
  | S f =>
      if Z.leb symnext sx then []
      else
        let dist := Z.land (sym sx) 255 + Z.shiftl (Z.land (sym (sx + 1)) 255) 8 in
        let lc   := sym (sx + 2) in
        (if Z.eqb dist 0 then TLit lc else TMatch (lc + MIN_MATCH) dist)
        :: sym_toks f sym (sx + 3) symnext
  end.

Definition sym_tokens (s : TSt) : list Tok :=
  sym_toks (Z.to_nat (ts_symnext s)) (ts_symbuf s) 0 (ts_symnext s).

(** cEnc — every token is representable: a literal is a byte, and a match
    has [MIN_MATCH <= len <= MAX_MATCH] and [1 <= dist <= 32768].
    These are exactly the ranges [compress_block] needs for
    [_length_code]/[d_code] to stay in their tables. *)
Definition tok_enc (t : Tok) : Prop :=
  match t with
  | TLit b => 0 <= b < 256
  | TMatch len dist => MIN_MATCH <= len <= MAX_MATCH /\ 1 <= dist <= 32768
  end.

Definition cEnc (ts : list Tok) : Prop := Forall tok_enc ts.

(** cRes — resolving the tokens against an initially empty history
    reproduces the input.  [copy_n] is the overlapping LZ77 copy. *)
Fixpoint copy_n (n : nat) (dist : Z) (out : list Z) : list Z :=
  match n with
  | O => out
  | S k => copy_n k dist (out ++ [nth (Z.to_nat (zlen out - dist)) out 0])
  end.

Definition resolve_tok (out : list Z) (t : Tok) : option (list Z) :=
  match t with
  | TLit b => Some (out ++ [u8 b])
  | TMatch len dist =>
      if (Z.leb 1 dist) && (Z.leb dist (zlen out))
      then Some (copy_n (Z.to_nat len) dist out) else None
  end.

Fixpoint resolve (out : list Z) (ts : list Tok) : option (list Z) :=
  match ts with
  | [] => Some out
  | t :: r => match resolve_tok out t with
              | None => None
              | Some out' => resolve out' r
              end
  end.

Definition cRes (input : list Z) (ts : list Tok) : Prop := resolve [] ts = Some input.

(** cEmpty — empty input yields no tokens. *)
Definition cEmpty (input : list Z) (ts : list Tok) : Prop := input = [] -> ts = [].

(** ** 20. Elementary facts

    Cheap, and used by the walk and by the round-trip lane.  The
    substantial obligations (Kraft, canonical lengths, the hash-chain
    invariant behind [cRes]) are model-level work for the round-trip lane;
    nothing here is stated without a proof. *)

Lemma it_zero_pointwise :
  forall n i a j, j < i \/ i + Z.of_nat n <= j -> arr_zero n i a j = a j.
Proof.
  induction n as [|n IH]; intros i a j H; cbn [arr_zero]; [reflexivity|].
  rewrite IH by lia. apply zset_other. lia.
Qed.

(** ** [bt_loop] fuel monotonicity and the combine-loop measure

    [build_tree] falls back to the UNCHANGED state if [bt_loop] runs out
    of fuel ([trees.c:671]'s [do..while] is bounded by [HEAP_SIZE]), so
    every downstream fact has to know the fuel was enough.  Monotonicity
    plus the measure is what makes that a one-line side condition. *)
Lemma bt_loop_fuel_mono :
  forall f f' st r,
    (f <= f')%nat -> bt_loop f st = Some r -> bt_loop f' st = Some r.
Proof.
  induction f as [|f IH]; intros f' st r Hle H; cbn [bt_loop] in H;
    [discriminate H|].
  destruct f' as [|f']; [lia|]. cbn [bt_loop].
  destruct (bt_step st); [apply IH; [lia | exact H] | exact H].
Qed.

(** THE MEASURE.  [pqremove] does [heap_len--] once per trip
    ([trees.c:486-491]) and the [while] runs while [heap_len >= 2], so
    [heap_len] is the decreasing quantity and [HEAP_SIZE] bounds it. *)
Definition bt_measure (st : BtSt) : Z := b_hlen st.

Lemma bt_step_decreases :
  forall st st', bt_step st = BtCont st' -> bt_measure st' = bt_measure st - 1.
Proof.
  intros st st' H. unfold bt_step in H. cbv zeta in H.
  destruct (Z.leb 2 (b_hlen st - 1)); [|discriminate H].
  injection H as H; subst st'. reflexivity.
Qed.

Lemma bt_step_cont_ge2 :
  forall st st', bt_step st = BtCont st' -> 2 <= bt_measure st'.
Proof.
  intros st st' H. unfold bt_step in H. cbv zeta in H.
  destruct (Z.leb 2 (b_hlen st - 1)) eqn:E; [|discriminate H].
  injection H as H; subst st'. unfold bt_measure. cbn [b_hlen].
  now apply Z.leb_le in E.
Qed.

(** [gen_bitlen]'s overflow adjust, likewise: the header claims [overflow]
    falls by 2 a trip; here that claim is checked. *)
Lemma gb_adjust_fuel_irrel :
  forall f f' maxlen blc ov,
    (S (Z.to_nat ov) <= f)%nat -> (f <= f')%nat ->
    gb_adjust f' maxlen blc ov = gb_adjust f maxlen blc ov.
Proof.
  induction f as [|f IH]; intros f' maxlen blc ov Hf Hle; [lia|].
  destruct f' as [|f']; [lia|]. cbn [gb_adjust].
  destruct (Z.ltb 2 ov) eqn:E; [|reflexivity].
  apply Z.ltb_lt in E. apply IH; lia.
Qed.

(** [arr_zero] as a RANGE fact, in [Base]'s vocabulary. *)
Lemma arr_zero_arr_eq_on :
  forall n i a lo hi,
    (hi <= i \/ i + Z.of_nat n <= lo) -> arr_eq_on (arr_zero n i a) a lo hi.
Proof.
  intros n i a lo hi H j Hj. apply it_zero_pointwise. lia.
Qed.

Lemma arr_zero_hit :
  forall n i a j, i <= j < i + Z.of_nat n -> arr_zero n i a j = 0.
Proof.
  induction n as [|n IH]; intros i a j H; cbn [arr_zero]; [lia|].
  destruct (Z.eq_dec j i) as [->|Hne].
  - rewrite it_zero_pointwise by lia. apply zset_same.
  - apply IH. lia.
Qed.

(** [copy_n] appends exactly [n] bytes. *)
Lemma copy_n_length :
  forall n d out, length (copy_n n d out) = (length out + n)%nat.
Proof.
  induction n as [|n IH]; intros d out; cbn [copy_n]; [lia|].
  rewrite IH, length_app. cbn [length]. lia.
Qed.

(** [copy_n] composes as a fuel: [n] then [m] bytes is [n + m] bytes.
    This is the fact every "split the match at a block boundary" step
    needs, and it is much cheaper to state here than to retrofit. *)
Lemma copy_n_add :
  forall n m d out, copy_n (n + m) d out = copy_n m d (copy_n n d out).
Proof.
  induction n as [|n IH]; intros m d out; cbn [copy_n Nat.add];
    [reflexivity | apply IH].
Qed.

(** THE APPEND CHARACTERISATION.  Every trip appends exactly one byte at
    the END, and that byte is read [d] back from the end as it stands. *)
Lemma copy_n_S_end :
  forall n d out,
    copy_n (S n) d out
    = copy_n n d out
      ++ [nth (Z.to_nat (zlen (copy_n n d out) - d)) (copy_n n d out) 0].
Proof.
  intros n d out. replace (S n) with (n + 1)%nat by lia.
  rewrite copy_n_add. cbn [copy_n]. reflexivity.
Qed.

Lemma copy_n_prefix :
  forall n d out, exists tl, copy_n n d out = out ++ tl /\ length tl = n.
Proof.
  induction n as [|n IH]; intros d out; cbn [copy_n].
  - exists []. rewrite app_nil_r. split; reflexivity.
  - destruct (IH d (out ++ [nth (Z.to_nat (zlen out - d)) out 0]))
      as [tl [Heq Hlen]].
    exists (nth (Z.to_nat (zlen out - d)) out 0 :: tl).
    rewrite Heq, <- app_assoc. split; [reflexivity | cbn [length]; lia].
Qed.

(** THE POINTWISE CHARACTERISATION, part 1: what was already there is
    untouched. *)
Lemma copy_n_nth_lt :
  forall n d out i, (i < length out)%nat -> nth i (copy_n n d out) 0 = nth i out 0.
Proof.
  intros n d out i Hi. destruct (copy_n_prefix n d out) as [tl [Heq _]].
  rewrite Heq. now rewrite app_nth1.
Qed.

(** …and part 2: the LZ77 recurrence itself — every produced byte equals
    the byte [d] positions earlier in the SAME list.  This is the form the
    window layer wants; the [d < len] run-length case is included, which
    is why the right-hand side reads from [copy_n n d out] and not from
    [out]. *)
Lemma copy_n_nth_ge :
  forall n d out i,
    1 <= d <= zlen out ->
    (length out <= i < length out + n)%nat ->
    nth i (copy_n n d out) 0 = nth (i - Z.to_nat d)%nat (copy_n n d out) 0.
Proof.
  intros n d out i Hd Hi.
  remember (i - length out)%nat as k eqn:Hkdef.
  assert (Hk : (k < n)%nat) by lia.
  assert (Hlen : length (copy_n k d out) = i)
    by (rewrite copy_n_length; lia).
  assert (Hzl : zlen out = Z.of_nat (length out)) by reflexivity.
  assert (Hstep : nth i (copy_n (S k) d out) 0
                  = nth (i - Z.to_nat d)%nat (copy_n k d out) 0).
  { rewrite copy_n_S_end. rewrite app_nth2 by lia.
    rewrite Hlen, Nat.sub_diag. cbn [nth]. f_equal.
    unfold zlen. rewrite Hlen. lia. }
  assert (Hn1 : copy_n n d out = copy_n (n - S k) d (copy_n (S k) d out))
    by (rewrite <- copy_n_add; f_equal; lia).
  assert (Hn2 : copy_n n d out = copy_n (n - k) d (copy_n k d out))
    by (rewrite <- copy_n_add; f_equal; lia).
  transitivity (nth i (copy_n (S k) d out) 0).
  { rewrite Hn1 at 1. apply copy_n_nth_lt. rewrite copy_n_length. lia. }
  rewrite Hstep. symmetry. rewrite Hn2 at 1.
  apply copy_n_nth_lt. rewrite Hlen. lia.
Qed.

(** THE SHIFT.  LZ77 distances are measured from the END of the history,
    so prefixing the history with [p] shifts the whole copy by [p] and
    changes nothing else.  (Soundness: [d <= zlen out] means every source
    index lands inside [out], never inside [p].) *)
Lemma copy_n_shift :
  forall n d p out,
    1 <= d <= zlen out -> copy_n n d (p ++ out) = p ++ copy_n n d out.
Proof.
  induction n as [|n IH]; intros d p out H; cbn [copy_n]; [reflexivity|].
  assert (Hx : nth (Z.to_nat (zlen (p ++ out) - d)) (p ++ out) 0
               = nth (Z.to_nat (zlen out - d)) out 0).
  { unfold zlen in *. rewrite length_app.
    rewrite app_nth2 by lia. f_equal. lia. }
  rewrite Hx, <- app_assoc. apply IH.
  unfold zlen in *. rewrite length_app. cbn [length]. lia.
Qed.

(** [resolve] only extends: the already-produced prefix is never rewritten.
    This is the fact the block-chaining argument uses at every boundary. *)
Lemma resolve_tok_prefix :
  forall out t out', resolve_tok out t = Some out' -> exists tl, out' = out ++ tl.
Proof.
  intros out [b|len dist] out' H; cbn [resolve_tok] in H.
  - inversion H; subst. now eexists.
  - destruct ((Z.leb 1 dist) && (Z.leb dist (zlen out))); [|discriminate].
    inversion H; subst. clear H.
    destruct (copy_n_prefix (Z.to_nat len) dist out) as [tl [Heq _]].
    now exists tl.
Qed.

Lemma resolve_prefix :
  forall ts out out', resolve out ts = Some out' -> exists tl, out' = out ++ tl.
Proof.
  induction ts as [|t r IH]; intros out out' H; cbn [resolve] in H.
  - inversion H; subst. exists []. now rewrite app_nil_r.
  - destruct (resolve_tok out t) as [o1|] eqn:H1; [|discriminate].
    apply resolve_tok_prefix in H1 as [t1 ->].
    apply IH in H as [t2 ->]. exists (t1 ++ t2). now rewrite app_assoc.
Qed.

(** ** [resolve] compositionality — the block-chaining kit

    Block chaining is literally unwritable without these two.  They are
    lean-zip's [resolveLZ77_shift] and its append companion. *)

Lemma resolve_app :
  forall t1 t2 out,
    resolve out (t1 ++ t2)
    = match resolve out t1 with
      | None => None
      | Some o => resolve o t2
      end.
Proof.
  induction t1 as [|t r IH]; intros t2 out; cbn [resolve app]; [reflexivity|].
  destruct (resolve_tok out t) as [o|]; [apply IH | reflexivity].
Qed.

Lemma resolve_tok_shift :
  forall p out t out',
    resolve_tok out t = Some out' -> resolve_tok (p ++ out) t = Some (p ++ out').
Proof.
  intros p out [b|len dist] out' H; cbn [resolve_tok] in H |- *.
  - injection H as H; subst out'. now rewrite app_assoc.
  - destruct (Z.leb 1 dist) eqn:H1; [|discriminate H].
    destruct (Z.leb dist (zlen out)) eqn:H2; [|discriminate H].
    cbn [andb] in H. injection H as H; subst out'.
    apply Z.leb_le in H1, H2.
    assert (Hz : Z.leb dist (zlen (p ++ out)) = true).
    { apply Z.leb_le. unfold zlen in *. rewrite length_app. lia. }
    rewrite Hz. replace (Z.leb 1 dist) with true by (symmetry; now apply Z.leb_le).
    cbn [andb]. f_equal. apply copy_n_shift. lia.
Qed.

(** THE SHIFT: a token list that resolves against an empty-er history
    resolves the same way against a longer one, producing the same bytes
    after the prefix.  Sound because LZ77 indices are measured from the
    front of what is still to come, i.e. from the END of the history. *)
Lemma resolve_shift :
  forall ts p out r,
    resolve out ts = Some r -> resolve (p ++ out) ts = Some (p ++ r).
Proof.
  induction ts as [|t rest IH]; intros p out r H; cbn [resolve] in H |- *.
  - injection H as H; subst r. reflexivity.
  - destruct (resolve_tok out t) as [o|] eqn:Ht; [|discriminate H].
    rewrite (resolve_tok_shift p out t o Ht). now apply IH.
Qed.

(** …and the corollary block chaining is actually spelled with.  NOTE the
    hypothesis: [t2] must resolve from an EMPTY history, i.e. it may not
    reach back into [t1]'s output.  Real deflate blocks DO reach back, so
    this is the clean-cut case (a [Z_FULL_FLUSH] boundary, or a stream
    whose second block happens not to); the general case is
    [resolve_app] with [resolve i1 t2] on the right. *)
Corollary cRes_app :
  forall t1 t2 i1 i2, cRes i1 t1 -> cRes i2 t2 -> cRes (i1 ++ i2) (t1 ++ t2).
Proof.
  intros t1 t2 i1 i2 H1 H2. unfold cRes in *.
  rewrite resolve_app, H1.
  pose proof (resolve_shift t2 i1 [] i2 H2) as Hs.
  rewrite app_nil_r in Hs. exact Hs.
Qed.

(** cEmpty is immediate for the empty token list, which is what every
    [deflate_*] tail produces when it never tallied. *)
Lemma cEmpty_nil : forall input, cEmpty input [].
Proof. intros input _. reflexivity. Qed.

Lemma cEnc_nil : cEnc [].
Proof. constructor. Qed.

Lemma cRes_nil : cRes [] [].
Proof. reflexivity. Qed.

(** [sym_toks] on an empty buffer is empty — the [cEmpty] side of a block
    that tallied nothing. *)
Lemma sym_tokens_empty : forall s, ts_symnext s = 0 -> sym_tokens s = [].
Proof.
  intros s H. unfold sym_tokens. rewrite H. reflexivity.
Qed.

(** ** 20b. A freshly allocated [trees.c] cluster

    [deflateInit2_] [ZALLOC]s [deflate_state] WITHOUT zeroing it
    ([deflate.c:432]; zlib's [zcalloc] is [malloc], not [calloc]), so
    [heap]/[depth]/[prev_match]/[match_start]/[heap_len]/[heap_max] hold
    allocator garbage until first written.  The model uses 0; nothing reads
    those slots before writing them (the harness records them as
    [Z_UNDEF_UNTIL_SET] for exactly this reason). *)
Definition ts_new : TSt :=
  {| ts_trees   := fun _ => tzero;
     ts_maxcode := fun _ => 0;
     ts_blcount := zzero;
     ts_heap    := zzero;
     ts_heaplen := 0;
     ts_heapmax := 0;
     ts_depth   := zzero;
     ts_symbuf  := zzero;
     ts_symnext := 0;
     ts_optlen  := 0;
     ts_statlen := 0;
     ts_matches := 0;
     ts_bw      := bw_init |}.

(** ** 21. Well-formedness of a [trees.c] call

    The hypotheses the C's own [Assert]s demand, collected so a
    machine-level walk can discharge them from the caller's invariant
    rather than re-deriving them. *)
Record tr_wf (s : TSt) (sym_end : Z) : Prop := mkTrWf {
  (** [trees.c:943]: [pending] must not have caught up with the unread
      symbols.  This is what lets the model keep [pending_buf] and
      [sym_buf] as two separate arrays. *)
  wf_no_overlay : 0 <= ts_symnext s <= sym_end;
  (** [bi_valid] is the count of pending bits, [< Buf_size]. *)
  wf_bivalid    : 0 <= bw_valid (ts_bw s) < Buf_size;
  (** [bi_buf] is a [ush] and its bits above [bi_valid] are zero
      ([deflate.h:270-273]). *)
  wf_bibuf      : 0 <= bw_buf (ts_bw s) < 2 ^ bw_valid (ts_bw s);
  (** every heap index the tree phases touch is in range *)
  wf_heap       : 0 <= ts_heaplen s < HEAP_SIZE /\ 0 <= ts_heapmax s <= HEAP_SIZE
}.
