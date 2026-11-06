(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v; 1536 of its 1692 lines of code are new or changed and 1217 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_write_value.v, with its numbers changed; 107 of its 179 lines of code are new or changed and 1620 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/ZZwv_defs.v, with its module paths changed; 62 of its 140 lines of code are new or changed and 101 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/ZZwv_defs.v (a working branch
   1a5dc5b2e7c): same names, every address, frame slot and register re-measured on fs.asan-ubsan; imports point at lib/B's
   image files and walk kit. The two call-composition steps wvc_after_call_ot / wvc_tail_otJ are NOT repeated here: they
   are proved in lib/B/FSW_write_value_entry.v (a Theorem Labs lane) and imported.
   rule 24: proves no function (kind: segment lemma) - the container arms of write_value B.
   write_value's CONTAINER arms (array / object), fs.asan-ubsan image B (write_value 0x84010, frame 192): the walk's
   symbolic states. MEASURED with the engine on the pinned fs.asan-ubsan (sha256 5ac5ce09..., a build machine, probe runs of
   this lane): from the entry state (FSW_write_value_entry.wv_ss0) the arms call put at 0x840d8 (returning to 0x840dc),
   then indent at 0x8419c (returning to 0x841a0), per item put_string of the key at 0x84214 (0x84218), put of the
   separator at 0x84224 (0x84228), write_value of the item at 0x8427c (0x84280), put of the comma at 0x84188 (0x8418c),
   the closing indent at 0x842c0 (0x842c4), and TAIL-jump to put with the closing bracket (j at 0x84440).
   Image B's frame (192 bytes): 8 = 3 (v & 7 + 3, the inline check's limit), 16 = v & 7 (= 0), 24 = the entry d (a3),
   32 = the separator length, 40 = shadow(v + 32), 48 = v + 32, 56 = the separator, 64 = ',', 72 = the shadow base,
   80 = shadow(v), 88 .. 184 = s11 .. s0, ra. The loop's registers: s0 = o, s1 = v, s2 = v + 40, s3 = pretty,
   s4 = shadow(v + 24), s5 = i, s6 = d + 1 (addiw), s7 = 56 i, s8 = v + 24, s9 = 8 i, s10 = the UBSan overflow flag of
   d + 1 (slt), s11 = shadow(v + 40).
   UBSan (trap mode, one `unimp` at 0x84444): nine guards are on these arms; the conditions below (wvc_cSLT ..
   wvc_cMULH) name the operands the engine meets at the ones it cannot decide from the atom facts alone, MEASURED.
   Rule 24 (proof-index, a Theorem Labs lane, unpiped): write_value has RELEASED proofs for fs's PLAIN and UBSAN
   builds only (lib/Prog, lib/U/Prog), none for an ASan image; 0x84010 is not in the released set. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_rres FSW_ret FSW_pj FSH_Fn_writer.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterValue PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================= the container arms' constants (MEASURED on fs.asan-ubsan) ================= *)
Definition WVC_F : Z := 192.                      (* lib/B/FSH_Base.FRAME_write_value *)
Definition WVC_CEIL : Z := 140737479966720.       (* 0x7fffff800000: alloc_ceiling's bound (YCbq.v asan_consts) *)
Definition WVC_R_OPEN  : Z := 0x840dc.            (* return of the put of '[' / '{' (jal at 0x840d8) *)
Definition WVC_R_IND   : Z := 0x841a0.            (* return of the per-item indent (jal at 0x8419c) *)
Definition WVC_R_KEY   : Z := 0x84218.            (* return of put_string of the key, object (jal at 0x84214) *)
Definition WVC_R_SEP   : Z := 0x84228.            (* return of the put of ':' / ': ', object (jal at 0x84224) *)
Definition WVC_R_ITEM  : Z := 0x84280.            (* return of the recursive write_value of the item (jal at 0x8427c) *)
Definition WVC_R_COMMA : Z := 0x8418c.            (* return of the put of ',' (jal at 0x84188) *)
Definition WVC_R_CLOSE : Z := 0x842c4.            (* return of the closing indent (jal at 0x842c0) *)
Definition WV_CONT_RAS : list Z :=
  [WVC_R_OPEN; WVC_R_IND; WVC_R_KEY; WVC_R_SEP; WVC_R_ITEM; WVC_R_COMMA; WVC_R_CLOSE].
(* the read-only literals the arms put (lib/B/FSH_Rt.FS_RO_STRS; the same addresses as image A's, MEASURED) *)
Definition WVC_LBRACKET : Z := 0x21180.
Definition WVC_LBRACE   : Z := 0x21160.
Definition WVC_RBRACKET : Z := 0x21220.
Definition WVC_RBRACE   : Z := 0x21200.
Definition WVC_COMMA    : Z := 0x211a0.
Definition WVC_COLON    : Z := 0x211e0.
Definition WVC_COLON_SP : Z := 0x211c0.
Definition wvc_open  (ty : Z) : Z := if ty =? 6 then WVC_LBRACE else WVC_LBRACKET.
Definition wvc_close (ty : Z) : Z := if ty =? 6 then WVC_RBRACE else WVC_RBRACKET.
Definition wvc_sep    (p : Z) : Z := if p =? 0 then WVC_COLON else WVC_COLON_SP.
Definition wvc_seplen (p : Z) : Z := if p =? 0 then 1 else 2.

(* ================= the resumed states ================= *)
(* the env at a resume: fs_extraT (atom 32 = the shadow base) ++ wvc_xs, i.e.
   xatom 0 .. 3 = the node's str / kids / keys / n, xatom 4 = the entry depth d,
   xatom 5 .. 17 = the thirteen saved entry registers in the order of the frame slots 88 .. 184
   (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra), xatom 18 = the address keys + 8 * i of the object key slot,
   xatom 19 = the key pointer read from it *)
Definition wvc_saved : list (bv 5) := [27; 26; 25; 24; 23; 22; 21; 20; 19; 18; 9; 8; 1]%bv.
Definition wvc_xs (regs : bvmap 5 word) (str kids keys n d ke key : Z) : list word :=
  [Z_to_bv 64 str; Z_to_bv 64 kids; Z_to_bv 64 keys; Z_to_bv 64 n; Z_to_bv 64 d]
  ++ map (fun r => YK11.getr regs r) wvc_saved
  ++ [Z_to_bv 64 ke; Z_to_bv 64 key].
(* the ASan shadow address of v + c, as the walk computes it *)
Definition wvc_shv (b : nat) (c : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff b c) (SLit 3)) (SOff 32 0).
(* the frame slots the entry run wrote (MEASURED at the jal to put, 0x840d8): 16 = v & 7 (the engine folds it to 0 by
   the node's alignment fact), 24 = the entry d, 72 = the shadow base, 80 = shadow(v), 88 .. 184 = the saved registers *)
Definition wvc_cs0 : list YP09.chunk :=
  [YP09.mkChunk 16 (CVal 8 (SLit 0)); YP09.mkChunk 24 (CVal 8 (SOff (xatom 4) 0));
   YP09.mkChunk 72 (CVal 8 (SOff 32 0)); YP09.mkChunk 80 (CVal 8 (wvc_shv 9 0))]
  ++ map (fun k => YP09.mkChunk (88 + 8 * Z.of_nat k) (CVal 8 (SOff (xatom (5 + k)) 0))) (seq 0 13).
(* ... and the slots the container arm's prelude adds before the item loop (MEASURED at 0x840f8 .. 0x84174) *)
Definition wvc_csL (p : Z) : list YP09.chunk :=
  [YP09.mkChunk 8 (CVal 8 (SLit 3)); YP09.mkChunk 32 (CVal 8 (SLit (wvc_seplen p)));
   YP09.mkChunk 40 (CVal 8 (wvc_shv 9 32)); YP09.mkChunk 48 (CVal 8 (SOff 9 32));
   YP09.mkChunk 56 (CVal 8 (SLit (wvc_sep p))); YP09.mkChunk 64 (CVal 8 (SLit WVC_COMMA))] ++ wvc_cs0.
(* the root node, based at the resumed s1 (atom 9) *)
Definition wvc_node (ty : Z) : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 56 0 0
    [YP09.mkChunk 0 (CVal 4 (SLit ty)); YP09.mkChunk 16 (CVal 8 (SOff (xatom 0) 0));
     YP09.mkChunk 24 (CVal 8 (SOff (xatom 1) 0)); YP09.mkChunk 32 (CVal 8 (SOff (xatom 2) 0));
     YP09.mkChunk 40 (CVal 8 (SOff (xatom 3) 0))].
(* the object's key slot keys + 8 * i, based at its own atom *)
Definition wvc_keyR : YP09.region :=
  YP09.mkRegion (Some (xatom 18)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff (xatom 19) 0))].
(* the atom facts. Node: 8-aligned, below the ceiling. In the loop states, MEASURED as what the UBSan guards need:
   s5 = i below 2 ^ 54 (atom 21: the guards 0x8424c (seqz of kids + 56 i) and the ranges of 56 i), kids >= 4096
   (xatom 1: 0x8424c `snez kids`), and for the object keys >= 4096 (xatom 2: 0x841d8 `snez keys`, 0x841e8 `beqz keys`)
   and the key slot keys + 8 i >= 4096, 8-aligned (xatom 18: 0x841d8 `seqz`, 0x841f4 the alignment) *)
Definition wvc_gf0 : list (nat * afact) := [(9%nat, mkAF 4096 (WVC_CEIL - 56) 3)].
Definition wvc_gfA : list (nat * afact) :=
  (21%nat, mkAF 0 (2 ^ 54 - 1) 0) :: (xatom 1, mkAF 4096 WVC_CEIL 0) :: wvc_gf0.
Definition wvc_gfK : list (nat * afact) :=
  (xatom 18, mkAF 4096 (WVC_CEIL - 8) 3) :: (xatom 19, mkAF 0 (2 ^ 64 - 1) 0) ::
  (xatom 2, mkAF 4096 WVC_CEIL 0) :: wvc_gfA.
Definition wvc_SH0 : list shent := [mkSHE 9 0 56].
Definition wvc_SHK : list shent := [mkSHE 9 0 56; mkSHE (xatom 18) 0 8].
Definition wvc_setr (ss : sstate) (l : list (bv 5 * sv)) : sstate :=
  mkSS (ss_pc ss) (fold_left (fun r q => sr_set r (fst q) (snd q)) l (ss_regs ss)) (ss_mem ss) (ss_resv ss)
    (ss_facts ss).
(* the state at WVC_R_OPEN: the frame and the node (image B keeps shadow(v) in the frame slot 80, no register) *)
Definition wvc_ssO (ty : Z) : sstate := fss_retT WVC_R_OPEN WVC_F wvc_cs0 [wvc_node ty] wvc_gf0.
(* the state at a loop resume point r (WVC_R_IND, _KEY, _SEP, _ITEM, _COMMA, _CLOSE): the prelude's slots, the key
   slot's region (OBJECT only), and the loop's registers; the two conditions the arm already took (pretty, n <> 0).
   The key slot keys + 8 * i is a region for the object (ty = 6) only: an array node's keys field is 0. The loop's key
   cursor (reg 25 = s9 = xatom 18 - xatom 2) is computed on both arms; s5 = i (reg 21) and s7 = 56 i (reg 23) stay the
   env's register atoms; s10 (reg 26) is 0: the open run's slt (d + 1 <s d) is 0 under wvc_cSLT. *)
Definition wvc_rsL (ty : Z) : list YP09.region := if ty =? 6 then [wvc_node ty; wvc_keyR] else [wvc_node ty].
Definition wvc_gfL (ty : Z) : list (nat * afact) := if ty =? 6 then wvc_gfK else wvc_gfA.
Definition wvc_SHL (ty : Z) : list shent := if ty =? 6 then wvc_SHK else wvc_SH0.
Definition wvc_Lregs : list (bv 5 * sv) :=
  [(18%bv, SOff 9 40); (20%bv, wvc_shv 9 24);
   (22%bv, SAluw ALU_ADD (SOff (xatom 4) 0) (SLit 1));
   (24%bv, SOff 9 24);
   (25%bv, SAlu ALU_SUB (SOff (xatom 18) 0) (SOff (xatom 2) 0));
   (26%bv, SLit 0); (27%bv, wvc_shv 9 40)].
Definition wvc_ssL (ty p r : Z) : sstate :=
  add_cond
    (add_cond
      (wvc_setr (fss_retT r WVC_F (wvc_csL p) (wvc_rsL ty) (wvc_gfL ty)) wvc_Lregs)
      (mkAC (if p =? 0 then BC_EQ else BC_NE) (SOff 19 0) (SLit 0)))
    (mkAC BC_NE (SOff (xatom 3) 0) (SLit 0)).
(* the state at WVC_R_CLOSE (after the closing indent): the loop state with the NODE ALONE for both arms and the node's
   atom fact only (after the last item the key cursor keys + 8 * n may lie past the object's keys block); the close
   run reads none of the loop's registers. *)
Definition wvc_ssN (ty p : Z) : sstate :=
  add_cond
    (add_cond
      (wvc_setr (fss_retT WVC_R_CLOSE WVC_F (wvc_csL p) [wvc_node ty] wvc_gf0) wvc_Lregs)
      (mkAC (if p =? 0 then BC_EQ else BC_NE) (SOff 19 0) (SLit 0)))
    (mkAC BC_NE (SOff (xatom 3) 0) (SLit 0)).

(* ================= the UBSan guards the engine cannot decide from the atom facts (MEASURED operands) =================
   Each is added to the state before the run that meets it (st_ok_add_cond), from the arm's premises:
   - wvc_cSLT, guard 0x8418c `bnez s10` (s10 = slt (addiw d 1) d, the signed overflow of d + 1) on the open run:
     d + 1 < 2 ^ 31, from write_value_spec_at's d + depth t <= 2 ^ 31 - 1 and depth (JArr / JObj _) >= 1;
   - wvc_cI60, guard 0x841e0 `bnez (srli s5 60)`: i < n < 2 ^ 54 (the node's n, pj_hdr / the tree's length);
   - wvc_cKEYS, guard 0x841e4 `bltu (keys + 8 i) keys`: keys + 8 n <= alloc_ceiling (the keys block, pj_hdr / pj_node);
   - wvc_cKIDS, guard 0x84250 `bltu (56 i + kids) kids`: kids + 56 n <= alloc_ceiling (the kids block);
   - wvc_cMULH, guard 0x84268 `bnez (snez (mulh i 56 ^ (56 i >>s 63)))`, the signed overflow of 56 i: 56 i < 2 ^ 63.
   The guards 0x841d8, 0x841e8, 0x841f4 and 0x8424c the engine decides from wvc_gfK / wvc_gfA. *)
Definition wvc_cSLT : acond :=
  mkAC BC_EQ (SAlu ALU_SLT (SAluw ALU_ADD (SOff (xatom 4) 0) (SLit 1)) (SOff (xatom 4) 0)) (SLit 0).
Definition wvc_cI60 : acond := mkAC BC_EQ (SAlu ALU_SRL (SOff 21 0) (SLit 60)) (SLit 0).
Definition wvc_cKEYS : acond := mkAC BC_GEU (SOff (xatom 18) 0) (SOff (xatom 2) 0).
Definition wvc_cKIDS : acond :=
  mkAC BC_GEU (SAlu ALU_ADD (SMd M_MUL (SOff 21 0) (SLit 56)) (SOff (xatom 1) 0)) (SOff (xatom 1) 0).
Definition wvc_cMULH : acond :=
  mkAC BC_EQ
    (SAlu ALU_SLTU (SLit 0)
       (SAlu ALU_XOR (SMd M_MULH (SOff 21 0) (SLit 56)) (SAlu ALU_SRA (SMd M_MUL (SOff 21 0) (SLit 56)) (SLit 63))))
    (SLit 0).

(* ---- what a walk holds at a point of the run: the symbolic state on the machine's memory, the shadow entries for
   the token run, the caller's journal over the unpoisoned memory, and ARU ---- *)
Definition wvc_at {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}
    (B : asyms) (E : env) (ss : sstate) (SH : list shent) (W : world tfibsegs) (ms : machine_state)
    (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world tfibsegs)
    (mem : word -> option byte) (md : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
    (U : list (Z * Z)) (mdc : Model) (k : Z) : Prop :=
  st_ok tfibsegs E ss (restrict (w_H W) ms) /\
  sh_ok tfibsegs fs_Bx SH E (mrestrict (w_H W) (ms_mem ms)) /\
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U (ms_mem ms)) mdc k /\
  ARU tfibsegs B lyc Sc U W (ms_mem ms) mdc.

(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance
   resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.
