(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/APgRt.v (the context record, rt_from, rt_entry,
   rt_E_havoc / rt_E_ewset, awrRT / keptRT / relowRT / rt_hand / rt_prelude, fs_roF / fs_rwF) and
   proofs/libreac/fuzz_knock/lib/A/APgLoop0.v (the shape of the shared cut states and their invariants) at
   origin/ossv/recipes 6ebe35ba632, made the interface of the walk of reac-pw/fuzz_pin's reac_box_pin_parse on image A
   (fuzz_pin.asan, 0x80b44, 832 bytes): the callee context record ppcx, the contract premises pp_pre / pp_base, the
   continuation pp_from (caller-journal form, the class-0 frame on the side stack for frames in the journal's own list,
   the kept-memory fact in lib/Reusable/YCbq.v's acall_kept form), the entry state ss_pp0 and pp_entry, the five cut
   states ss_P1 ss_P2 ss_PL ss_P3 ss_P4 with their invariants, and the statements of the six segment lemmas.

   rule 24: no function is proved here.

   THE CODE (neutral excerpt of 0x80b44-0x80e84; image A addresses)
   - 0x80b44-0x80b88: 160-byte save area (ra at sp-8, s0..s11 at sp-16 .. sp-104), s0 = entry sp, `andi sp,sp,-0x20`,
     s1 = sp1 = 32 * ((sp - 160) / 32), s8 = lb, s10 = mo, s5 = sa, s3 = SB (read through the cell 0x99050).
   - 0x80bb4-0x80bb8: a0 = 0x40, call of the class-0 frame allocation of the side stack for frames; s2 = s11 = F.
   - 0x80bec-0x80c48: F spilled at sp1+0x30; header words at F; s4 = SB + F/8; the 8 shadow bytes of F become
     f1 f1 f1 f1 f8 f3 f3 f3; a3 = -1.                                                   -> cut P1 at 0x80c4c
   - 0x80c4c-0x80c6c: sa = 0, the instrumented check of the byte at sa, lb = 0, mo = 0, s = [] -> 0x80d9c.
                                                                                         -> cut P2 at 0x80c70
   - 0x80c70-0x80cbc: SB spilled at sp1+0x18; strcspn wrapper (s9 = toklen); the count cell's shadow byte := 0;
     catalogue call; s3 = 11; mo, lb spilled at sp1+8 / sp1+0x10; s7 = s8 = cat; s6 = SB + cat/8.
                                                                                         -> cut PL at 0x80cc0
   - the loop at 0x80cc0 over the rows; found row -> cut P3 at 0x80d08; after row 10 -> 0x80d94.
   - 0x80d08-0x80d90: the label, the two out-cell stores, a3 = 0. 0x80d94-0x80d98: shadow byte 4 := 0xf8.
                                                                                         -> cut P4 at 0x80d9c
   - 0x80d9c-0x80e3c: F[0] := 0x45E0360E, the shadow bytes := 0xf5, the flag byte := 0, a0 = a3, restore, ret.

   THE ENV SLOTS (atoms). 0..31 = the entry registers, 32 = SB (Ereg regs pp_extra). The context record pins
   70 = sp1, 75 = F = frame_addr lyc 0 fpos, 87 = FL = flag_addr lyc 0 fpos, 88 = SB + F/8 (pp_E). The walk's own
   atoms, bound by the invariants: 100 = toklen (PN_tl), 102 = the row address (PN_row), 103 = the rows left
   (PN_cnt), 104 = the result word a3 at P4 (PN_rc). The dead registers of each cut state are fresh atoms of a
   window: P2 320, PL 280, P3 240, P4 200 (ss_P1 is the engine's own state, with the class-0 call's fresh atoms
   71..86); each window lies below the atoms of every state that joins into it, so the join's havoc is free (the
   engine's fresh atoms after a call or a shadow load start above the state's highest atom).
   A segment adds its own atoms at or above PP_N0 = 400.
   REGION ORDER at every cut: shadow of F (88) :: frame F (75) :: the sp1 spills (70; not at P4) :: the save area (2).
   The frame's shadow region is read-only at every cut (the token runner cannot justify a writable window in the
   shadow band); pp_fs_rw / pp_fs_ro re-window it for the shadow stores. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YI16 YM05 YCeo.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import PPgBase PPgCSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ===================== 0. constants ===================== *)
Definition A_PARSE : Z := 0x80b44.
(* the ':' set string strcspn reads (`auipc a0,0xfffa0` 0x80c78 + `addi a1,a0,0x108`) *)
Definition PP_COLON : Z := 0x20d80.
(* the catalogue entry `jal 0x80f7c` at 0x80c94 *)
Definition A_CATALOGUE : Z := 0x80f7c.
(* the entry valuation's extra slot 32 = SB, as knock's rt_extra *)
Definition pp_extra : list word := [Z_to_bv 64 SB].
(* the token runner's shadow base and band, as knock's RTBx / RTBspan *)
Definition PPBx : sv := SOff 32 0.
Definition PPBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* the walk's own atoms *)
Definition PN_tl : nat := 100.
Definition PN_row : nat := 102.
Definition PN_cnt : nat := 103.
Definition PN_rc : nat := 104.
(* the dead-register windows and the floor of a segment's own atoms *)
(* (P1 has no window: it is the engine's own state after the class-0 call, whose fresh atoms are 71..86) *)
Definition PW_P2 : nat := 320.
Definition PW_PL : nat := 280.
Definition PW_P3 : nat := 240.
Definition PW_P4 : nat := 200.
Definition PP_N0 : nat := 400.
(* the shadow byte values as the engine stores them (`sb` of the 64-bit register: -15, -8, -13) *)
Definition PP_F1 : Z := 18446744073709551601.
Definition PP_F8 : Z := 18446744073709551608.
Definition PP_F3 : Z := 18446744073709551603.

(* ===================== 2. the context record ===================== *)
(* everything tpin_parse_specX quantifies, then fpos (the class-0 frame's position), sp1 and E0 (the entry valuation) *)
Record ppcx := mkPPCX {
c_STK : Z; c_sp0 : Z; c_FP : list (Z * Z); c_ly : alayout; c_S : astate; c_W0 : world tfibsegs;
c_mem0 : word -> option byte; c_md0 : Model; c_own : list (Z * Z);
c_lyc : alayout; c_Sc : astate; c_W : world tfibsegs; c_memc : word -> option byte; c_mdc : Model;
c_k : Z; c_regs : bvmap 5 word; c_ch : list (Z * Z * Z);
c_sa : Z; c_mo : Z; c_lb : Z; c_s : list byte; c_cidm : Z; c_posm : Z; c_cidl : Z; c_posl : Z;
c_fpos : Z; c_sp1 : Z; c_E0 : env }.
Definition pp_with (cx : ppcx) (fpos sp1 : Z) (E0 : env) : ppcx :=
mkPPCX (c_STK cx) (c_sp0 cx) (c_FP cx) (c_ly cx) (c_S cx) (c_W0 cx) (c_mem0 cx) (c_md0 cx) (c_own cx)
(c_lyc cx) (c_Sc cx) (c_W cx) (c_memc cx) (c_mdc cx) (c_k cx) (c_regs cx) (c_ch cx)
(c_sa cx) (c_mo cx) (c_lb cx) (c_s cx) (c_cidm cx) (c_posm cx) (c_cidl cx) (c_posl cx) fpos sp1 E0.
Definition pp_F (cx : ppcx) : Z := frame_addr (c_lyc cx) 0 (c_fpos cx).
Definition pp_FL (cx : ppcx) : Z := flag_addr (c_lyc cx) 0 (c_fpos cx).
(* the bytes the walk may change that the caller sees: the two out-cells of a live call *)
Definition pp_oc (cx : ppcx) (a : Z) : Prop :=
pin_parse_live (c_sa cx) (c_mo cx) (c_lb cx) = true /\ pin_out_cell (c_mo cx) (c_lb cx) a.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* every premise of tpin_parse_specX tfibsegs B MT RLO RHI 0x80b44 cat 0x20d80 TP DP at cx, in its order *)
Definition pp_pre (B : asyms) (MT : ameter_ops) (RLO RHI cat : Z) (TP DP : nat -> Z) (cx : ppcx) : Prop :=
pin_pre_kit tfibsegs B (c_STK cx) (c_sp0 cx) (c_FP cx) (c_ly cx) (c_S cx) (c_W0 cx) (c_mem0 cx) (c_md0 cx) (c_own cx)
 (c_lyc cx) (c_Sc cx) (c_W cx) (c_memc cx) (c_mdc cx) (c_k cx) (c_regs cx) (c_ch cx) T_parse_STK EV_parse /\
getr (c_regs cx) 10 = w64 (c_sa cx) /\ getr (c_regs cx) 11 = w64 (c_mo cx) /\ getr (c_regs cx) 12 = w64 (c_lb cx) /\
0 <= c_sa cx < 2 ^ 64 /\ 0 <= c_mo cx < 2 ^ 64 /\ 0 <= c_lb cx < 2 ^ 64 /\
(c_sa cx <> 0 -> pin_spec_str tfibsegs (mrestrict (w_H (c_W cx)) (c_memc cx)) (aview tfibsegs (w_H (c_W cx)) (c_memc cx))
 (c_regs cx) T_parse_STK (c_sa cx) (c_s cx) /\
 exists b m, In (b, m) (ablocks B (c_lyc cx) (c_Sc cx)) /\ b <= c_sa cx /\
 c_sa cx + Z.of_nat (length (c_s cx)) + 1 <= b + req_size m) /\
(pin_parse_live (c_sa cx) (c_mo cx) (c_lb cx) = true ->
 c_mo cx mod 8 = 0 /\ c_lb cx mod 8 = 0 /\ (c_mo cx + 8 <= c_lb cx \/ c_lb cx + 8 <= c_mo cx) /\
 In (c_cidm cx, c_posm cx) (c_own cx) /\ 0 <= c_cidm cx /\ frame_addr (c_lyc cx) (c_cidm cx) (c_posm cx) mod 8 = 0 /\
 frame_addr (c_lyc cx) (c_cidm cx) (c_posm cx) <= c_mo cx /\
 c_mo cx + 8 <= frame_addr (c_lyc cx) (c_cidm cx) (c_posm cx) + fs_frame_bytes (c_cidm cx) /\
 In (c_cidl cx, c_posl cx) (c_own cx) /\ 0 <= c_cidl cx /\ frame_addr (c_lyc cx) (c_cidl cx) (c_posl cx) mod 8 = 0 /\
 frame_addr (c_lyc cx) (c_cidl cx) (c_posl cx) <= c_lb cx /\
 c_lb cx + 8 <= frame_addr (c_lyc cx) (c_cidl cx) (c_posl cx) + fs_frame_bytes (c_cidl cx) /\
 afobj tfibsegs B (c_lyc cx) (c_Sc cx) (c_W cx) (c_memc cx) (c_mo cx) 8 /\
 afobj tfibsegs B (c_lyc cx) (c_Sc cx) (c_W cx) (c_memc cx) (c_lb cx) 8 /\
 (forall x, pin_out_cell (c_mo cx) (c_lb cx) x -> ~ (spZ (c_regs cx) - T_parse_STK <= x < spZ (c_regs cx))) /\
 (forall x, pin_out_cell (c_mo cx) (c_lb cx) x -> ~ (c_sa cx <= x <= c_sa cx + Z.of_nat (length (c_s cx))))) /\
pin_ro_str tfibsegs (mrestrict (w_H (c_W cx)) (c_memc cx)) (aview tfibsegs (w_H (c_W cx)) (c_memc cx)) PP_COLON pin_colon_bytes /\
(forall x, PP_COLON <= x <= PP_COLON + 1 -> ~ (spZ (c_regs cx) - T_parse_STK <= x < spZ (c_regs cx))) /\
pin_cat_ok tfibsegs (mrestrict (w_H (c_W cx)) (c_memc cx)) (aview tfibsegs (w_H (c_W cx)) (c_memc cx)) cat TP DP /\
pin_cat_off_stack cat TP (c_regs cx) T_parse_STK /\
arodata_okP tfibsegs RLO RHI B (aview tfibsegs (w_H (c_W cx)) (c_memc cx)) /\
pin_ro_law tfibsegs B RLO RHI cat TP DP PP_COLON /\
count_cid 0 (frames (c_Sc cx)) < fs_frames 0.

(* pp_pre, sp1 and the entry valuation E0 *)
Definition pp_base (B : asyms) (MT : ameter_ops) (RLO RHI cat : Z) (TP DP : nat -> Z) (cx : ppcx) : Prop :=
pp_pre B MT RLO RHI cat TP DP cx /\
c_sp1 cx = 32 * ((spZ (c_regs cx) + -160) / 32) /\
(forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (c_E0 cx) n = getr (c_regs cx) r) /\
ew (c_E0 cx) 32 = Z_to_bv 64 SB.

(* E agrees with E0 on the entry slots and pins the context record's atoms *)
Definition pp_E (cx : ppcx) (E : env) : Prop :=
(forall n, (n < 33)%nat -> ew E n = ew (c_E0 cx) n) /\
ew E 70 = Z_to_bv 64 (c_sp1 cx) /\ ew E 75 = Z_to_bv 64 (pp_F cx) /\
ew E 87 = Z_to_bv 64 (pp_FL cx) /\ ew E 88 = Z_to_bv 64 (SB + pp_F cx / 8).

Definition pp_post (B : asyms) (MT : ameter_ops) (RLO RHI cat : Z) (TP DP : nat -> Z) (cx : ppcx)
: world tfibsegs -> config -> Prop :=
pin_post_parse tfibsegs B MT (c_STK cx) (c_sp0 cx) (c_FP cx) (c_ly cx) (c_S cx) (c_W0 cx) (c_mem0 cx) (c_md0 cx)
(c_own cx) (c_k cx) (c_regs cx) cat DP (c_sa cx) (c_mo cx) (c_lb cx) (c_s cx)
(c_lyc cx) (c_Sc cx) (c_W cx) (c_memc cx) (c_mdc cx).

(* the kept-memory fact, lib/Reusable/YCbq.v:826 *)
Definition pp_KE (B : asyms) (cx : ppcx) (WN : world tfibsegs) (memN : word -> option byte) : Prop :=
acall_kept tfibsegs B (c_lyc cx) (c_Sc cx) (c_W cx) (c_memc cx) WN memN
(spZ (c_regs cx) - T_parse_STK) (spZ (c_regs cx)) (pp_oc cx).

Definition ppinv : Type := ppcx -> env -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop.

(* the continuation: from a state that ss / INV describe, the run reaches pp_post *)
Definition pp_from (B : asyms) (MT : ameter_ops) (RLO RHI cat : Z) (TP DP : nat -> Z) (ss : sstate) (INV : ppinv) : Prop :=
forall (cx : ppcx) (E : env) lyN SN (WN : world tfibsegs) (msN : machine_state) mdN,
pp_base B MT RLO RHI cat TP DP cx -> pp_E cx E ->
ajournal tfibsegs B (c_STK cx) (c_sp0 cx) (c_FP cx) (c_ly cx) (c_S cx) (c_W0 cx) (c_mem0 cx) (c_md0 cx)
 ((0, c_fpos cx) :: c_own cx) lyN SN WN (ms_mem msN) mdN (c_k cx) ->
frames SN = (0, c_fpos cx) :: frames (c_Sc cx) ->
Permutation (ablocks B lyN SN) (ablocks B (c_lyc cx) (c_Sc cx)) ->
mo_le MT (c_Sc cx) SN 0 -> same_io (c_mdc cx) mdN -> wle (c_W cx) WN ->
pp_KE B cx WN (ms_mem msN) ->
INV cx E lyN SN WN msN mdN ->
st_ok tfibsegs E ss (restrict (w_H WN) msN) ->
SRr tfibsegs WN (mkCfg msN mdN) (pp_post B MT RLO RHI cat TP DP cx).
End b.

(* ===================== 3. the entry state ===================== *)
(* the stack region covers [sp - 176, sp): sp1 >= sp - 176, and the spills at sp1+8 .. sp1+56 lie below sp - 104 *)
Definition pp_regions0 : smem := [ stack_region 176; got_region; bcell_region 32; uar_got_region; uar_cell_region ].
(* sp in [2^46, 2^47], 16-aligned; sa = a0 in [0, 2^47 - 2] (amem_range); slot 32 = SB *)
Definition pp_atoms0 : list (nat * afact) :=
[ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 0 (2 ^ 47 - 2) 0); (32%nat, mkAF SB SB 0) ].
Definition ss_pp0 : sstate := mkSS A_PARSE sr_atoms pp_regions0 None (mkFacts pp_atoms0 [] []).

(* ===================== 4. the memory shape of the cut states ===================== *)
(* the 8 shadow bytes of F: f1 f1 f1 f1 (b4) f3 f3 f3, read-only; b4 = f8, or 0 while the count cell is usable *)
Definition pp_rshadow (b4 : Z) : YP09.region :=
YP09.mkRegion (Some 88%nat) 0 8 0 0
[YP09.mkChunk 0 (CVal 1 (SLit PP_F1)); YP09.mkChunk 1 (CVal 1 (SLit PP_F1));
 YP09.mkChunk 2 (CVal 1 (SLit PP_F1)); YP09.mkChunk 3 (CVal 1 (SLit PP_F1));
 YP09.mkChunk 4 (CVal 1 (SLit b4));
 YP09.mkChunk 5 (CVal 1 (SLit PP_F3)); YP09.mkChunk 6 (CVal 1 (SLit PP_F3)); YP09.mkChunk 7 (CVal 1 (SLit PP_F3))].
(* the 64-byte frame, writable; the flag pointer the allocation left at F + 56 *)
Definition pp_rframe : YP09.region :=
YP09.mkRegion (Some 75%nat) 0 64 0 64 [YP09.mkChunk 56 (CVal 8 (SOff 87 0))].
(* the spills off sp1: F at +0x30 (0x80bec) *)
Definition pp_rspill0 : YP09.region :=
YP09.mkRegion (Some 70%nat) 8 56 8 56 [YP09.mkChunk 48 (CVal 8 (SOff 75 0))].
(* and mo at +8, lb at +0x10 (0x80ca8 / 0x80cac), SB at +0x18 (0x80c70) *)
Definition pp_rspillL : YP09.region :=
YP09.mkRegion (Some 70%nat) 8 56 8 56
[YP09.mkChunk 8 (CVal 8 (SOff 11 0)); YP09.mkChunk 16 (CVal 8 (SOff 12 0));
 YP09.mkChunk 24 (CVal 8 (SOff 32 0)); YP09.mkChunk 48 (CVal 8 (SOff 75 0))].
(* the save area as the prologue writes it (0x80b4c-0x80b7c): s11 at sp-104 .. ra at sp-8 *)
Definition pp_saves : list YP09.chunk :=
[ YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0));
  YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
  YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
  YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
  YP09.mkChunk (-8) (CVal 8 (SOff 1 0)) ].
Definition pp_rsave : YP09.region := YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 pp_saves.
(* the context record's atoms: 88 = SB + F/8, 87 = FL, 75 = F, 70 = sp1, 2 = entry sp, 32 = SB *)
Definition pp_atomsC : list (nat * afact) :=
[ (88%nat, mkAF (SB + 512) (SB + 2 ^ 44) 2); (87%nat, HPTR 0); (75%nat, HPTR 5); (70%nat, mkAF (2 ^ 46 - 512) (2 ^ 47) 5);
  (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0) ].
(* the alias that makes SB + (F >> 3) the atom 88 *)
Definition pp_alias : list (sv * sv) := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 75 0) (SLit 3)) (SOff 32 0), SOff 88 0)].
(* the call is live: sa, mo, lb are pointers (sa in a heap block, mo and lb 8-aligned cells of caller frames) *)
Definition pp_atomsLive : list (nat * afact) := [ (10%nat, HPTR 0); (11%nat, HPTR 3); (12%nat, HPTR 3) ].
(* the row address (cat + 0x128 i < 2 ^ 47 - 296 from pin_cat_ok's amem_range, 8-aligned) and toklen; the row's
   range keeps its 8-byte shadow check and the check of row + 8 inside the shadow band (YCbn.v ob_in_span) *)
Definition pp_atomsRow : list (nat * afact) := [ (PN_row, mkAF 0 (2 ^ 47 - 16) 3); (PN_tl, mkAF 0 (2 ^ 32 - 1) 0) ].
Definition pp_atomsCnt : list (nat * afact) := [ (PN_cnt, mkAF 1 11 0) ].

(* ===================== 5. the five cut states ===================== *)
(* P1, 0x80c4c `beqz s5`: the frame is built. The state the engine leaves after 0x80b44-0x80c48 (the class-0 call's
   fresh atoms 71..86 in ra, t0-t2, a4-a7, t3-t6), with the frame's shadow made read-only and the four cell regions
   dropped. Live: sp = s1 = sp1, gp, tp, s0 = entry sp, a3 = -1, s2 = s11 = F, s3 = SB, s4 = SB + F/8, s5 = sa,
   s8 = lb, s10 = mo. *)
Definition ss_P1 : sstate := Eval vm_compute in
mkSS 0x80c4c
[SLit 0; SOff 71 0; SOff 70 0; SOff 3 0; SOff 4 0; SOff 72 0; SOff 73 0; SOff 74 0; SOff 2 0; SOff 70 0;
 SLit PP_F1; SLit 68317; SLit 527172; SLit 18446744073709551615; SOff 79 0; SOff 80 0;
 SOff 81 0; SOff 82 0; SOff 75 0; SOff 32 0; SOff 88 0; SOff 10 0; SOff 22 0; SOff 23 0; SOff 12 0; SOff 25 0;
 SOff 11 0; SOff 75 0; SOff 83 0; SOff 84 0; SOff 85 0; SOff 86 0]
[ YP09.mkRegion (Some 88%nat) 0 8 0 0
  [YP09.mkChunk 3 (CVal 1 (SLit PP_F1)); YP09.mkChunk 2 (CVal 1 (SLit PP_F1));
   YP09.mkChunk 1 (CVal 1 (SLit PP_F1)); YP09.mkChunk 0 (CVal 1 (SLit PP_F1));
   YP09.mkChunk 7 (CVal 1 (SLit PP_F3)); YP09.mkChunk 6 (CVal 1 (SLit PP_F3));
   YP09.mkChunk 5 (CVal 1 (SLit PP_F3)); YP09.mkChunk 4 (CVal 1 (SLit PP_F8))];
  YP09.mkRegion (Some 75%nat) 0 64 0 64
  [YP09.mkChunk 16 (CVal 8 (SLit 527172)); YP09.mkChunk 8 (CVal 8 (SLit 68317));
   YP09.mkChunk 0 (CVal 8 (SLit 1102416563)); YP09.mkChunk 56 (CVal 8 (SOff 87 0))];
  pp_rspill0; pp_rsave ]
None
(mkFacts (pp_atomsC ++ [(10%nat, mkAF 0 (2 ^ 47 - 2) 0)]) [] pp_alias).

(* P2, 0x80c70 `sd s3,0x18(s1)`: the call is live. Live: as P1 without a3. *)
Definition pp_deads_P2 : list nat := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 22; 23; 25; 28; 29; 30; 31]%nat.
Definition ss_P2_0 : sstate :=
mkSS 0x80c70
[SLit 0; SOff 1 0; SOff 70 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SOff 2 0; SOff 70 0;
 SOff 10 0; SOff 11 0; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0; SOff 16 0; SOff 17 0;
 SOff 75 0; SOff 32 0; SOff 88 0; SOff 10 0; SOff 22 0; SOff 23 0; SOff 12 0; SOff 25 0; SOff 11 0; SOff 75 0;
 SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0]
[pp_rshadow PP_F8; pp_rframe; pp_rspill0; pp_rsave]
None
(mkFacts (pp_atomsC ++ pp_atomsLive) [] pp_alias).
Definition ss_P2 : sstate := Eval vm_compute in ss_havoc_regs ss_P2_0 PW_P2 pp_deads_P2.

(* PL, 0x80cc0 the loop head at row i: s3 = rows left (PN_cnt), s6 = SB + row/8 in the form the token runner reads
   as a shadow load (YCbn.v match_x), s7 = s8 = the row address (PN_row), s9 = toklen (PN_tl), s5 = sa; the
   count cell's shadow byte is 0; the spills mo, lb, SB, F. *)
Definition pp_deads_PL : list nat := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 26; 28; 29; 30; 31]%nat.
Definition pp_s6row : sv := SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff PN_row 0) (SLit 3)).
Definition ss_PL_0 : sstate :=
mkSS 0x80cc0
[SLit 0; SOff 1 0; SOff 70 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SOff 2 0; SOff 70 0;
 SOff 10 0; SOff 11 0; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0; SOff 16 0; SOff 17 0;
 SOff 75 0; SOff PN_cnt 0; SOff 88 0; SOff 10 0; pp_s6row; SOff PN_row 0; SOff PN_row 0; SOff PN_tl 0; SOff 26 0; SOff 75 0;
 SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0]
[pp_rshadow 0; pp_rframe; pp_rspillL; pp_rsave]
None
(mkFacts (pp_atomsC ++ pp_atomsLive ++ pp_atomsRow ++ pp_atomsCnt) [] pp_alias).
Definition ss_PL : sstate := Eval vm_compute in ss_havoc_regs ss_PL_0 PW_PL pp_deads_PL.

(* P3, 0x80d08 `add a0,s5,s9`: row i's token is the spec's token. Live: s5 = sa, s7 = s8 = row, s9 = toklen. *)
Definition pp_deads_P3 : list nat := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 22; 26; 28; 29; 30; 31]%nat.
Definition ss_P3_0 : sstate :=
mkSS 0x80d08
[SLit 0; SOff 1 0; SOff 70 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SOff 2 0; SOff 70 0;
 SOff 10 0; SOff 11 0; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0; SOff 16 0; SOff 17 0;
 SOff 75 0; SOff 19 0; SOff 88 0; SOff 10 0; SOff 22 0; SOff PN_row 0; SOff PN_row 0; SOff PN_tl 0; SOff 26 0; SOff 75 0;
 SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0]
[pp_rshadow 0; pp_rframe; pp_rspillL; pp_rsave]
None
(mkFacts (pp_atomsC ++ pp_atomsLive ++ pp_atomsRow) [] pp_alias).
Definition ss_P3 : sstate := Eval vm_compute in ss_havoc_regs ss_P3_0 PW_P3 pp_deads_P3.

(* P4, 0x80d9c `lui a0,0x45e03`: the frame is given back from here. Live: gp, tp, s0 = entry sp, a3 = the result
   word (PN_rc), s2 = s11 = F, s4 = SB + F/8; the shadow is f1 f1 f1 f1 f8 f3 f3 f3 again. *)
Definition pp_deads_P4 : list nat :=
[1; 2; 5; 6; 7; 9; 10; 11; 12; 14; 15; 16; 17; 19; 21; 22; 23; 24; 25; 26; 28; 29; 30; 31]%nat.
Definition ss_P4_0 : sstate :=
mkSS 0x80d9c
[SLit 0; SOff 1 0; SOff 2 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SOff 2 0; SOff 9 0;
 SOff 10 0; SOff 11 0; SOff 12 0; SOff PN_rc 0; SOff 14 0; SOff 15 0; SOff 16 0; SOff 17 0;
 SOff 75 0; SOff 19 0; SOff 88 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 75 0;
 SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0]
[pp_rshadow PP_F8; pp_rframe; pp_rsave]
None
(mkFacts pp_atomsC [] pp_alias).
Definition ss_P4 : sstate := Eval vm_compute in ss_havoc_regs ss_P4_0 PW_P4 pp_deads_P4.

(* ===================== 6. the invariants =====================
   Every invariant and every segment statement takes the uniform prefix (B MT RLO RHI cat TP DP), used or not. *)
Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Definition INV_P1 (B : asyms) (MT : ameter_ops) (RLO RHI cat : Z) (TP DP : nat -> Z) : ppinv :=
fun cx E lyN SN WN msN mdN => True.
Definition INV_P2 (B : asyms) (MT : ameter_ops) (RLO RHI cat : Z) (TP DP : nat -> Z) : ppinv :=
fun cx E lyN SN WN msN mdN =>
pin_parse_live (c_sa cx) (c_mo cx) (c_lb cx) = true /\ c_s cx <> [].
(* row i is next; no row before it has the spec's token *)
Definition INV_PL (B : asyms) (MT : ameter_ops) (RLO RHI cat : Z) (TP DP : nat -> Z) (i : nat) : ppinv :=
fun cx E lyN SN WN msN mdN =>
pin_parse_live (c_sa cx) (c_mo cx) (c_lb cx) = true /\ c_s cx <> [] /\ (i < CAT_N)%nat /\
ew E PN_tl = Z_to_bv 64 (Z.of_nat (colon_idx (c_s cx))) /\
ew E PN_row = Z_to_bv 64 (row_addr cat i) /\
ew E PN_cnt = Z_to_bv 64 (11 - Z.of_nat i) /\
(forall j, (j < i)%nat -> tok_bytes j <> pin_token (c_s cx)).
(* row i is the first row whose token is the spec's token *)
Definition INV_P3 (B : asyms) (MT : ameter_ops) (RLO RHI cat : Z) (TP DP : nat -> Z) : ppinv :=
fun cx E lyN SN WN msN mdN =>
exists i, pin_parse_live (c_sa cx) (c_mo cx) (c_lb cx) = true /\ c_s cx <> [] /\ (i < CAT_N)%nat /\
ew E PN_tl = Z_to_bv 64 (Z.of_nat (colon_idx (c_s cx))) /\
ew E PN_row = Z_to_bv 64 (row_addr cat i) /\
tok_bytes i = pin_token (c_s cx) /\ pin_row (c_s cx) = Some i.
(* a3 is the result word; the out-cells hold the result *)
Definition INV_P4 (B : asyms) (MT : ameter_ops) (RLO RHI cat : Z) (TP DP : nat -> Z) : ppinv :=
fun cx E lyN SN WN msN mdN =>
ew E PN_rc = Z_to_bv 64 (parse_rc (pin_parse_res cat DP (c_sa cx) (c_mo cx) (c_lb cx) (c_s cx))) /\
(forall row lab, pin_parse_res cat DP (c_sa cx) (c_mo cx) (c_lb cx) (c_s cx) = Some (row, lab) ->
 val_mem tfibsegs (mrestrict (w_H WN) (ms_mem msN)) (c_mo cx) 8%nat row /\
 val_mem tfibsegs (mrestrict (w_H WN) (ms_mem msN)) (c_lb cx) 8%nat lab).

(* ===================== 7. the segment statements (each owner proves exactly its own) ===================== *)
(* PPgParse0.v pp_seg0: 0x80b44 -> 0x80c4c *)
Definition PP_seg0 (B : asyms) (MT : ameter_ops) (RLO RHI cat : Z) (TP DP : nat -> Z) : Prop :=
pp_from B MT RLO RHI cat TP DP ss_P1 (INV_P1 B MT RLO RHI cat TP DP) ->
forall cx, pp_pre B MT RLO RHI cat TP DP cx ->
SRr tfibsegs (c_W cx) (cfg_at tfibsegs A_PARSE (c_regs cx) (c_memc cx) (c_mdc cx)) (pp_post B MT RLO RHI cat TP DP cx).
(* PPgParse1.v pp_seg1: 0x80c4c -> 0x80c70 | 0x80d9c *)
Definition PP_seg1 (B : asyms) (MT : ameter_ops) (RLO RHI cat : Z) (TP DP : nat -> Z) : Prop :=
pp_from B MT RLO RHI cat TP DP ss_P2 (INV_P2 B MT RLO RHI cat TP DP) ->
pp_from B MT RLO RHI cat TP DP ss_P4 (INV_P4 B MT RLO RHI cat TP DP) ->
pp_from B MT RLO RHI cat TP DP ss_P1 (INV_P1 B MT RLO RHI cat TP DP).
(* PPgParse2.v pp_seg2: 0x80c70 -> 0x80cc0 at row 0 *)
Definition PP_seg2 (B : asyms) (MT : ameter_ops) (RLO RHI cat : Z) (TP DP : nat -> Z) : Prop :=
pp_from B MT RLO RHI cat TP DP ss_PL (INV_PL B MT RLO RHI cat TP DP 0) ->
pp_from B MT RLO RHI cat TP DP ss_P2 (INV_P2 B MT RLO RHI cat TP DP).
(* PPgParse2L.v pp_seg2L: 0x80cc0 at row i -> 0x80d08 | 0x80d9c (induction on the rows left) *)
Definition PP_seg2L (B : asyms) (MT : ameter_ops) (RLO RHI cat : Z) (TP DP : nat -> Z) : Prop :=
pp_from B MT RLO RHI cat TP DP ss_P3 (INV_P3 B MT RLO RHI cat TP DP) ->
pp_from B MT RLO RHI cat TP DP ss_P4 (INV_P4 B MT RLO RHI cat TP DP) ->
forall i, pp_from B MT RLO RHI cat TP DP ss_PL (INV_PL B MT RLO RHI cat TP DP i).
(* PPgParse3.v pp_seg3: 0x80d08 -> 0x80d9c *)
Definition PP_seg3 (B : asyms) (MT : ameter_ops) (RLO RHI cat : Z) (TP DP : nat -> Z) : Prop :=
pp_from B MT RLO RHI cat TP DP ss_P4 (INV_P4 B MT RLO RHI cat TP DP) ->
pp_from B MT RLO RHI cat TP DP ss_P3 (INV_P3 B MT RLO RHI cat TP DP).
(* PPgParse4.v pp_seg4: 0x80d9c -> ret *)
Definition PP_seg4 (B : asyms) (MT : ameter_ops) (RLO RHI cat : Z) (TP DP : nat -> Z) : Prop :=
pp_from B MT RLO RHI cat TP DP ss_P4 (INV_P4 B MT RLO RHI cat TP DP).
End i.

(* ===================== 8. the context record's lemmas and the entry ===================== *)
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* [knock A/APgRt.v:118-129 rt_E_havoc / rt_E_ewset] *)
Lemma pp_E_havoc : forall cx E N vs, (89 <= N)%nat -> pp_E cx E -> pp_E cx (havoc E N vs).
Proof.
intros cx E N vs HN (AG & E70 & E75 & E87 & E88). unfold pp_E. rewrite !ew_havoc_old by lia.
split; [|split; [exact E70 | split; [exact E75 | split; [exact E87 | exact E88]]]].
intros n Hn. rewrite ew_havoc_old by lia. apply AG. exact Hn.
Qed.
Lemma pp_E_ewset : forall cx E n w, (89 <= n)%nat -> pp_E cx E -> pp_E cx (ewset E n w).
Proof.
intros cx E n w HN (AG & E70 & E75 & E87 & E88). unfold pp_E. rewrite !ew_ewset_other by lia.
split; [|split; [exact E70 | split; [exact E75 | split; [exact E87 | exact E88]]]].
intros m Hm. rewrite ew_ewset_other by lia. apply AG. exact Hm.
Qed.
(* the post and the premises do not read fpos, sp1 or E0 *)
Lemma pp_post_with : forall B MT RLO RHI cat TP DP cx fpos sp1 E0,
pp_post B MT RLO RHI cat TP DP (pp_with cx fpos sp1 E0) = pp_post B MT RLO RHI cat TP DP cx.
Proof. reflexivity. Qed.
Lemma pp_pre_with : forall B MT RLO RHI cat TP DP cx fpos sp1 E0,
pp_pre B MT RLO RHI cat TP DP (pp_with cx fpos sp1 E0) = pp_pre B MT RLO RHI cat TP DP cx.
Proof. reflexivity. Qed.
(* the read-only bytes the contract's arodata_okP names stay as they were along the kept-memory fact, when the
   [RLO, RHI) window lies in the image (the Section hypothesis RELRO of every walk file); with pin_ro_law_at
   (PPgCSpec.v) this gives pin_cat_ok / pin_ro_str at any state of the walk *)
Lemma pp_arodata_kept : forall B RLO RHI lyc Sc W memc WN memN slo shi (Er : Z -> Prop),
(forall a, RLO <= a < RHI -> in_img tfibsegs a) ->
acall_kept tfibsegs B lyc Sc W memc WN memN slo shi Er ->
arodata_okP tfibsegs RLO RHI B (aview tfibsegs (w_H W) memc) ->
arodata_okP tfibsegs RLO RHI B (aview tfibsegs (w_H WN) memN).
Proof.
intros B RLO RHI lyc Sc W memc WN memN slo shi Er HRL (_ & _ & K3 & _) HR a Hro Ho He.
rewrite (K3 a); [exact (HR a Hro Ho He) | | exact Ho | exact He].
destruct Hro as [(s0 & Hs & _ & Hr) | Hgot]; [exists s0; split; [exact Hs | exact Hr] | exact (HRL a Hgot)].
Qed.
(* a region kept by a callee whose post keeps every byte outside its stack window (and outside its own excluded
   set): the form of the wrappers' posts (PPgParseLib.v aj_strcspn_at / aj_strlen_at / aj_strncmp_at) and of
   pin_post_simple (the catalogue). The window's bytes must be present after the call. *)
Lemma pp_region_kept_out : forall E H H2 (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview tfibsegs H2 m2 a = aview tfibsegs H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
region_kept tfibsegs E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H H2 m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview tfibsegs). apply Hav. exact Ha.
- intros _. apply (apresent_writable tfibsegs). apply Hp. exact Ha.
Qed.
(* frame and flag addresses depend on ly_F only, which layout_le keeps *)
Lemma pp_frame_addr_eq : forall n1 n2 ly ly1 ly2 c p,
layout_le n1 ly ly1 -> layout_le n2 ly ly2 -> frame_addr ly2 c p = frame_addr ly1 c p.
Proof.
intros n1 n2 ly ly1 ly2 c p (_ & _ & _ & _ & _ & F1 & _) (_ & _ & _ & _ & _ & F2 & _).
unfold frame_addr. rewrite F1, F2. reflexivity.
Qed.
Lemma pp_flag_addr_eq : forall n1 n2 ly ly1 ly2 c p,
layout_le n1 ly ly1 -> layout_le n2 ly ly2 -> flag_addr ly2 c p = flag_addr ly1 c p.
Proof.
intros n1 n2 ly ly1 ly2 c p (_ & _ & _ & _ & _ & F1 & _) (_ & _ & _ & _ & _ & F2 & _).
unfold flag_addr. rewrite F1, F2. reflexivity.
Qed.
(* the entry state at 0x80b44 [knock A/APgRt.v:157-217 rt_entry, from the contract's premises] *)
Lemma pp_entry : forall B MT RLO RHI cat TP DP (cx : ppcx), TfibLib B -> AR_laws tfibsegs B ->
pp_pre B MT RLO RHI cat TP DP cx ->
st_ok tfibsegs (Ereg (c_regs cx) pp_extra) ss_pp0
(restrict (w_H (c_W cx)) (mkst (c_regs cx) (Z_to_bv 64 A_PARSE) (c_memc cx) (seg_rom tfibsegs))).
Proof.
intros B MT RLO RHI cat TP DP cx TL LAWS HPRE.
destruct cx as [STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch sa mo lb s cidm posm cidl posl fpos sp1 E0].
unfold pp_pre in HPRE.
cbn [c_STK c_sp0 c_FP c_ly c_S c_W0 c_mem0 c_md0 c_own c_lyc c_Sc c_W c_memc c_mdc c_k c_regs c_ch
 c_sa c_mo c_lb c_s c_cidm c_posm c_cidl c_posl c_fpos c_sp1 c_E0] in HPRE |- *.
destruct HPRE as (HKIT & H10 & _ & _ & Hsa & _ & _ & Hstr & _).
destruct HKIT as (HJ & _ & _ & _ & _ & _ & Hal16 & HspLo & HspHi & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
destruct Hstk as (_ & HSTK & Hceil & Hslo & Hshi & H47 & _ & _ & _).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
change T_parse_STK with 8400 in HspLo.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (tl_got_shadow B TL), (tl_shadow_cell B TL) in Kgot. rewrite (tl_shadow_cell B TL) in Kcell.
rewrite (tl_got_uar B TL), (tl_uar_cell B TL) in Kguar. rewrite (tl_uar_cell B TL) in Kuar.
assert (Hsa47 : sa <= 2 ^ 47 - 2).
{ destruct (Z.eq_dec sa 0) as [->|Hne]; [lia|].
  destruct (Hstr Hne) as ((_ & _ & _ & _ & _ & _ & _ & _ & Ham & _) & _).
  unfold amem_range in Ham. rewrite C3, C4, C5 in Ham. lia. }
clear Hstr.
rewrite restrict_mkst_fx.
set (E := Ereg regs pp_extra).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 sa) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
unfold ss_pp0. apply (entry_st_ok_full tfibsegs); change (Ereg regs pp_extra) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold pp_regions0, stack_region, got_region, bcell_region, uar_got_region, uar_cell_region.
repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable tfibsegs). apply Hpres. lia.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold A_GOT_shadow.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 626768) at 1.
apply (chunk_ok_val tfibsegs E _ 0 626768 8 (SLit A_shadow_glob) A_shadow_glob); [reflexivity | unfold A_shadow_glob; zside | zside |].
exact (val_mem_of_rdword tfibsegs (w_H W) memc _ _ Kgot).
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold A_shadow_glob.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 660984) at 1.
apply (chunk_ok_val tfibsegs E _ 0 660984 8 (SOff 32 0) SB);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
exact (val_mem_of_rdword tfibsegs (w_H W) memc _ _ Kcell).
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold A_GOT_uar.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 626856) at 1.
apply (chunk_ok_val tfibsegs E _ 0 626856 8 (SLit A_uar_glob) A_uar_glob); [reflexivity | unfold A_uar_glob; zside | zside |].
exact (val_mem_of_rdword tfibsegs (w_H W) memc _ _ Kguar).
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold A_uar_glob.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 660992) at 1.
apply (chunk_ok_val tfibsegs E _ 0 660992 4 (SLit 1) 1); [reflexivity | zside | zside |].
exact (val_mem_of_rd32 tfibsegs (w_H W) memc _ _ Kuar).
- apply pairwise_disjoint_of_extents.
unfold pp_regions0, stack_region, got_region, bcell_region, uar_got_region, uar_cell_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp.
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert HspLo HspHi Hslo Hshi H47 Hceil C1 HSTK. clear. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok pp_atoms0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32. rewrite !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert HspLo HspHi Hslo Hshi H47 Hceil C1 HSTK Hal16 Hsa Hsa47. clear. unfold SB. intros.
repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.
End e.

(* ===================== 9. the tactics of the walk (class 0, the caller-journal form) ===================== *)
(* pp_prelude: the start of every segment lemma `pp_from .. ss INV` [knock A/APgRt.v:299-342 rt_prelude, with the
   ppcx fields and the class-0 frame]. Names it leaves: the ppcx fields (STK sp0 FP ly S W0 mem0 md0 own lyc Sc W
   memc mdc k regs ch sa mo lb s cidm posm cidl posl fpos sp1 E0); E lyN SN WN msN mdN; HBASE0 (pp_base, for
   pp_hand); HJ (journal), Hfrs, HPERM, HMLE, HIO, HWLE, HKE (acall_kept, the excluded set unfolded), HINV (INV
   unfolded), HS (st_ok); the premises H10 H11 H12 Hsa Hmo Hlb Hstr Hlive Hcolon Hcolst Hcat Hcatst HROD Hrolaw
   Hcnt0, HJ0 Hret Hra4 Hgp Htp Hch Hal16 HspLo (sp0 - STK <= spZ regs - 8400) HspHi Hev, HAR0 HLY0 Hpres0,
   Hceil Hslo Hshi H47; AG (agreement below 33), E70 E75 E87 E88 (F and FL folded), E10 E11 E12 E2 E32, EE, Usp
   (bv_unsigned (ew E0 2) = spZ regs), Esp1, Hsp1 (spZ regs - 176 <= sp1 <= spZ regs - 160), Hsp1al Hsp1al16;
   HARN (AR now), EFA / EFL (frame_addr / flag_addr at lyN = at lyc), Hfin (In (0, fpos) (frames SN)), F, FL (set),
   HFal HFlo HFpres HFSpres HF4096 HFceil HFhigh HFimg, HF8 HF8lo HF8hi HF8c; C1..C5, Hes, Hwx, Hsegs. *)
Ltac pp_prelude :=
let LAWS := rnLAWS in
let cx := fresh "cx" in
intros cx E lyN SN WN msN mdN HBASE HEE HJ Hfrs HPERM HMLE HIO HWLE HKE HINV HS;
destruct cx as [STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch sa mo lb s cidm posm cidl posl fpos sp1 E0];
pose proof HBASE as HBASE0;
unfold pp_base, pp_pre in HBASE; unfold pp_E, pp_F, pp_FL in HEE; unfold pp_KE, pp_oc in HKE; red in HINV;
cbn [c_STK c_sp0 c_FP c_ly c_S c_W0 c_mem0 c_md0 c_own c_lyc c_Sc c_W c_memc c_mdc c_k c_regs c_ch
 c_sa c_mo c_lb c_s c_cidm c_posm c_cidl c_posl c_fpos c_sp1 c_E0] in HBASE, HEE, HJ, Hfrs, HPERM, HMLE, HIO, HWLE, HKE, HINV;
destruct HBASE as (HPRE & Esp1 & EE & E32);
destruct HPRE as (HKIT & H10 & H11 & H12 & Hsa & Hmo & Hlb & Hstr & Hlive & Hcolon & Hcolst & Hcat & Hcatst & HROD & Hrolaw & Hcnt0);
destruct HKIT as (HJ0 & Hret & Hra4 & Hgp & Htp & Hch & Hal16 & HspLo & HspHi & Hev);
change T_parse_STK with 8400 in HspLo;
destruct HEE as (AG & E70 & E75 & E87 & E88);
pose proof Hwx_tfa as Hwx; pose proof tfib_segs_low as Hsegs;
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5);
assert (Hes : ESTACK = 4096) by reflexivity;
pose proof HJ0 as (HAR0 & HLY0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _ & _);
assert (E10 : ew E0 10 = Z_to_bv 64 sa) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10);
assert (E11 : ew E0 11 = Z_to_bv 64 mo) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11);
assert (E12 : ew E0 12 = Z_to_bv 64 lb) by (rewrite (EE 12%nat 12%bv eq_refl); exact H12);
assert (E2 : ew E0 2 = getr regs 2) by (exact (EE 2%nat 2%bv eq_refl));
assert (Usp : bv_unsigned (ew E0 2) = spZ regs) by (rewrite E2; reflexivity);
pose proof (proj1 HJ) as HARN;
assert (EFA : forall c p, frame_addr lyN c p = frame_addr lyc c p)
 by (let c := fresh "c" in let p := fresh "p" in intros c p; exact (pp_frame_addr_eq _ _ _ _ _ c p HLY0 (proj1 (proj2 HJ))));
assert (EFL : forall c p, flag_addr lyN c p = flag_addr lyc c p)
 by (let c := fresh "c" in let p := fresh "p" in intros c p; exact (pp_flag_addr_eq _ _ _ _ _ c p HLY0 (proj1 (proj2 HJ))));
assert (Hfin : In (0, fpos) (frames SN)) by (rewrite Hfrs; left; reflexivity);
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HARN Hfin) as (HFal & [HFlo _] & HFpres & HFSpres);
destruct (frames_bounds tfibsegs _ LAWS _ _ _ _ _ 0 fpos HARN Hfin) as (HF4096 & HFceil & HFhigh);
pose proof (frm_off_img _ _ _ _ _ _ _ _ HARN Hfin) as HFimg;
change (fs_frame_bytes 0) with 64 in HFlo, HFpres, HFSpres, HFceil, HFhigh, HFimg;
change (64 / 8) with 8 in HFSpres;
rewrite !EFA in HFal, HFlo, HFpres, HFSpres, HF4096, HFceil, HFhigh, HFimg;
set (F := frame_addr lyc 0 fpos) in *; set (FL := flag_addr lyc 0 fpos) in *;
assert (HF8 : F / 8 = 4 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)) as Dq; rewrite HFal, Z.add_0_r in Dq;
 rewrite Dq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity);
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia);
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia);
assert (HF8c : 8 * (F / 8) <= F) by (apply Z.mul_div_le; clear; lia);
let Hsp1r := fresh "Hsp1r" in let Hsp1al := fresh "Hsp1al" in let Hsp1al16 := fresh "Hsp1al16" in
destruct (sp1_facts (spZ regs + -160) ltac:(clear - Hceil Hslo HspLo C1; lia)
 ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16);
rewrite <- Esp1 in Hsp1r, Hsp1al, Hsp1al16;
assert (Hsp1 : spZ regs - 176 <= sp1 <= spZ regs - 160) by (clear - Hsp1r; lia); clear Hsp1r.

(* write ranges of a run [knock A/APgRt.v:220-249 awrRT, class 0]: the frame's shadow (88) and the frame (75) are
   in_frames of the class-0 frame (0, fpos); the save area (2) and the spills (70) lie in the caller's stack window;
   a read-only region needs nothing; any other writable region (an out-cell at mo or lb) is paid by octac, which
   gets the goal `awr_byte .. a` with Ha : b + wlo <= a < b + whi in context. *)
Ltac ppAWR_rec AG fpos F EFA octac :=
lazymatch goal with
| |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
| |- awr_ok _ (YP09.mkRegion _ _ _ ?wlo ?whi _ :: _) _ _ _ _ _ _ _ =>
first
[ lazymatch (eval vm_compute in (Z.leb whi wlo)) with true => apply awr_ok_cons_ro; [clear; cbn; lia|] end
| lazymatch goal with
  | |- awr_ok _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
    eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 88%nat); [reflexivity | evalE AG | | ];
    [ cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      right; right; right; exists 0, fpos; split; [left; reflexivity|]; right;
      unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8;
      rewrite ?EFA; fold F; unfold SB; clear - Ha; lia
    | ]
  | |- awr_ok _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
    eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 75%nat); [reflexivity | evalE AG | | ];
    [ cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      right; right; right; exists 0, fpos; split; [left; reflexivity|]; left;
      unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 0) with 64; rewrite ?EFA; fold F; clear - Ha; lia
    | ]
  | |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) ?stk ?s0 _ _ _ _ _ =>
    lazymatch goal with Hlo : s0 - stk <= ?spv - 8400, Hhi : ?spv <= s0 |- _ =>
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - s0));
    [reflexivity | evalE AG | clear - Hlo Hhi; cbn; lia | clear - Hlo Hhi; cbn; lia |] end
  | |- awr_ok _ (YP09.mkRegion (Some 70%nat) _ _ _ _ _ :: _) ?stk ?s0 _ _ _ _ _ =>
    lazymatch goal with Hs1 : ?spv - 176 <= ?s1 <= ?spv - 160, Hlo : s0 - stk <= ?spv - 8400, Hhi : ?spv <= s0 |- _ =>
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 70%nat (s1 - s0));
    [reflexivity | evalE AG | clear - Hs1 Hlo Hhi; cbn; lia | clear - Hs1 Hlo Hhi; cbn; lia |] end
  end
| lazymatch goal with |- awr_ok _ (YP09.mkRegion (Some ?n) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
    eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ n); [reflexivity | evalE AG | | ];
    [ cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; octac | ] end
| match goal with |- awr_ok _ (?r :: _) _ _ _ _ _ _ _ => idtac "PPAWR-HEAD" r end; fail 1 "ppAWR: no rule for the head region" ];
ppAWR_rec AG fpos F EFA octac
end.
Ltac ppAWR AG fpos F EFA octac :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
ppAWR_rec AG fpos F EFA octac.

(* the regions a callee keeps [knock A/APgRt.v:250-279 keptRT, class 0]: HK is the callee's acall_kept, HJx the
   caller journal after the call; ErT closes `~ Er a` for the callee's excluded set, PrT `apresent` of a window. *)
Ltac ppKEPT HK HJx AG ErT PrT :=
lazymatch goal with
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj tfibsegs _); [exact HK | exact HJx | evalE AG | lia | lia | lia | lia | lia]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 70%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj tfibsegs _); [exact HK | exact HJx | evalE AG | lia | lia | lia | lia | lia]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj tfibsegs _); [exact HK | evalE AG | eassumption
| left; rewrite_frame_addr; change (fs_frame_bytes 0) with 64; lia | intros a Ha; cbn beta; first [exact (fun Hn : False => Hn) | ErT] | intros a Ha; PrT ]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj tfibsegs _); [exact HK | evalE AG | eassumption
| right; rewrite_frame_addr; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; unfold SB; lia
| intros a Ha; cbn beta; first [exact (fun Hn : False => Hn) | ErT] | intros a Ha; first [lia | PrT] ]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some ?n) _ _ ?wlo ?whi _) =>
lazymatch goal with Hb : ew _ n = Z_to_bv 64 ?b |- _ =>
let L := rnLAWS in
first
[ lazymatch (eval vm_compute in (Z.leb whi wlo)) with true =>
first [ eapply (region_kept_block_aj tfibsegs _ _ _ _ _ _ _ _ _ _ _ n _ _ _ _ _ b); [exact HK | evalE AG | eassumption | lia | rqs_goal; lia | lia | intros a Ha Hn; first [exact Hn | ErT] ]
| eapply (region_kept_frame_aj tfibsegs _ _ _ _ _ _ _ _ _ _ _ n _ _ _ _ _ b); [exact HK | evalE AG | eassumption | rewrite_frame_addr; lia | rewrite_frame_addr; lia | lia | intros a Ha Hn; first [exact Hn | ErT] ] ] end
| eapply (region_kept_block_ajw2 tfibsegs _ L _ _ _ _ _ _ _ _ _ _ n _ _ _ _ _ b); [exact HK | exact (proj1 HJx) | eassumption | evalE AG | eassumption | lia | rqs_goal; lia | lia | lia | intros a Ha Hn; first [exact Hn | ErT] ]
| match goal with |- ?g => idtac "PPKEPT-FAIL" g end; fail ] end
end.
(* the regions a callee keeps when its post keeps every byte outside a window [lo, hi) (and outside its excluded
   set): HKW : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) [-> ~ Er a] -> aview H2 m2 a = aview H m a.
   Each side goal of HKW is closed by lia (the context must place the region away from the window) or by ErT;
   PrT proves `apresent H2 m2 a` for a byte a of a writable window (Ha : b + wlo <= a < b + whi). *)
Ltac ppKEPTO HKW AG ErT PrT :=
lazymatch goal with
| |- region_kept _ _ _ _ (YP09.mkRegion (Some ?n) _ _ _ _ _) =>
eapply (pp_region_kept_out _ _ _ _ _ n);
[ evalE AG
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply HKW; first [cbv beta; lia | ErT]
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; first [exfalso; lia | PrT] ]
| |- ?g => idtac "PPKEPTO-FAIL" g; fail
end.

(* a hypothesis about an entry slot (n < 33), re-stated for the current valuation [knock relowRT] *)
Ltac ppLOW HS AG H Hn :=
try clear Hn;
lazymatch type of HS with st_ok _ ?Ev _ _ =>
lazymatch type of H with ew _ ?n = ?v => assert (Hn : ew Ev n = v) by (rewrite (AG n) by lia; exact H) end end.

(* hand the current state to the next segment's continuation RC : pp_from .. ss INV [knock rt_hand]. Leaves the
   goals it cannot close by assumption, in pp_from's order (journal, frames, Permutation, mo_le, same_io, wle, KE),
   and the invariant (unfolded). *)
Ltac pp_hand RC HS :=
lazymatch goal with |- SRr _ ?W3 (mkCfg ?ms3 ?md3) (pp_post _ _ _ _ _ _ _ ?cxv) =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
eapply (RC cxv Ev _ _ W3 ms3 md3);
[ lazymatch goal with H0 : pp_base _ _ _ _ _ _ _ _ |- _ => exact H0 end
| repeat (lazymatch goal with |- pp_E _ (havoc _ _ _) => apply pp_E_havoc; [clear; cbn; lia|] | |- pp_E _ (ewset _ _ _) => apply pp_E_ewset; [clear; cbn; lia|] end);
  unfold pp_E, pp_F, pp_FL; cbn [c_lyc c_fpos c_E0 c_sp1];
  split; [assumption|]; repeat (split; [eassumption|]); eassumption
| first [eassumption | idtac]
| first [eassumption | idtac]
| first [eassumption | idtac]
| first [eassumption | idtac]
| first [eassumption | idtac]
| first [eassumption | idtac]
| first [eassumption | idtac]
| red; cbn [c_STK c_sp0 c_FP c_ly c_S c_W0 c_mem0 c_md0 c_own c_lyc c_Sc c_W c_memc c_mdc c_k c_regs c_ch
   c_sa c_mo c_lb c_s c_cidm c_posm c_cidl c_posl c_fpos c_sp1 c_E0]
| exact HS ] end end.

(* the frame's 8 shadow bytes: make the region writable (0, 8) before a shadow store, read-only again after
   [knock A/APgRt.v:343-364 fs_roF / fs_rwF, window 0 8]. Hp : forall i, 0 <= i < 8 -> apresent (w_H W) m
   (shadow_addr F + i) /\ _ at the CURRENT memory (al_frames at the current AR, as HFSpres of pp_prelude). *)
Ltac pp_fs_ro HS :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 88%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_region tfibsegs Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow tfibsegs Ex _ r 0 0 (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Ltac pp_fs_rw HS E88 Hp :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 88%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_region tfibsegs Ex ssx msx i r (set_window r 0 8) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow tfibsegs Ex _ r 0 8 (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite E88, unsigned_lit_small by (unfold SB; lia);
intros o Ho; apply (apresent_writable tfibsegs); unfold shadow_addr in Hp; rewrite <- SB_SHADOW_OFF in Hp;
apply (proj1 (Hp o ltac:(clear - Ho; lia)))))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.

(* the write range of the run that stores the flag byte (aj_run_flag_sh / aj_run_flag) [knock A/APgMain7.v:167-182
   wrangeRT, class 0]: every writable byte of the state is the caller's stack, the class-0 frame or its shadow, or
   the flag byte. *)
Ltac ppWRANGE AG fpos F FL EFA EFL :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros a (r & Hin & Hr); rewrite ?EFA, ?EFL; fold F FL;
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; intros Hr;
first [ exfalso; clear - Hr; lia
| right; clear - Hr; lia
| left; left; lazymatch goal with Hlo : ?s0 - ?stk <= ?spv - 8400, Hhi : ?spv <= ?s0 |- _ => clear - Hr Hlo Hhi; lia end
| left; right; right; right; exists 0, fpos; split; [left; reflexivity|];
  first [ left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 0) with 64; rewrite ?EFA; fold F; clear - Hr; lia
  | right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; rewrite ?EFA; fold F; unfold SB; clear - Hr; lia ]
| match goal with |- ?g => match type of Hr with ?t => idtac "PPWR-FAIL" t g end end; fail 2 "ppWRANGE" ]
| ]);
destruct Hin.

(* ===================== 10. the join tools =====================
   Fresh atoms, register re-pointing, facts and the join into a cut state's dead-register window. pin's AWalkFw2 is
   knock's and carries none of them; these are knock's, as reac-pw/fuzz_qdisc's lib/A/QPgLoop0.v carries them. *)
Section jw. Context {fx : YK11.FPState}.
(* [knock A/APgLoop0.v:101-102, the donor's A/ACf9.v:339-340] *)
Lemma denot_havoc_win : forall E k ws e, sv_atoms_on (win_free k (length ws)) e = true -> sv_denot (havoc E k ws) e = sv_denot E e.
Proof. intros E k ws e He. apply (sv_denot_agree_on (win_free k (length ws)) E); [apply env_agree_on_havoc | exact He]. Qed.
End jw.
(* [knock A/APgMain4.v:112-116 rt_atoms_ok_In]: the fact the state carries for an atom *)
Lemma pp_atoms_ok_In : forall E l n f, atoms_ok E l -> In (n, f) l -> afact_ok E n f.
Proof.
induction l as [|[n' f'] l IH]; cbn; intros n f H Hin; [destruct Hin|].
destruct H as [H1 H2]. destruct Hin as [Heq|Hin]; [injection Heq as -> ->; exact H1 | apply IH; assumption].
Qed.
(* [knock A/APgLoop0.v:156-157, the donor's A/ACf9.v:347-348] *)
Ltac ewpeel := repeat (first [ rewrite ew_havoc_old by nat_side | rewrite ew_havoc_above by nat_side | rewrite ew_ewset_other by nat_side ]).
Ltac ewpeel_in H := repeat (first [ rewrite ew_havoc_old in H by nat_side | rewrite ew_havoc_above in H by nat_side | rewrite ew_ewset_other in H by nat_side ]).
(* [knock A/APgLoop0.v:159-164, the donor's A/ACf9.v:246-251]: a fresh atom n with value w (n must be free in the
   state); En : ew (havoc Ev n [w]) n = w *)
Ltac add_atom_win HS n w En :=
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
let HS3 := fresh "HS3" in
pose proof (st_ok_havoc_win tfibsegs n Ev ssv msv [w] HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
assert (En : ew (havoc Ev n [w]) n = w) by (exact (ew_havoc_new _ n [w] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
(* [knock A/APgLoop0.v:166-193, the donor's A/ACf9.v:252-279]: the join into a cut state `target` whose dead
   registers `deads` (a list of bv 5, in the order of the state's pp_deads_* list) take the window from N: keep the
   target's regions (submem), havoc the dead registers' current values into N.., run `hook` (set the live
   registers / add the facts the target names), keep the target's facts, and change the state into `target`. *)
Ltac ra_join_win HS target N deads hook :=
norm_ss HS;
let tg := eval red in target in
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let rs := eval cbn [ss_mem] in (ss_mem tg) in
pose proof (st_ok_submem tfibsegs Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS;
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let dl := eval cbv in deads in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl) in
let vals' := eval cbn [map ms_regs restrict] in vals in
pose proof (st_ok_havoc_win tfibsegs N Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
set_regs_rec HS N vals' 0%nat dl end;
norm_ss HS;
hook;
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let fa := eval cbn [ss_facts f_atoms] in (f_atoms (ss_facts tg)) in
let cs := eval cbn [ss_facts f_conds] in (f_conds (ss_facts tg)) in
let al := eval cbn [ss_facts f_alias] in (f_alias (ss_facts tg)) in
pose proof (st_ok_facts_incl3 tfibsegs Ex ssx msx fa cs al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS;
lazymatch type of HS with st_ok _ _ ?ssx _ => first [change ssx with target in HS | idtac "JOIN-MISMATCH" ssx tg] end.
(* the cut states' dead registers as bv 5 lists, for ra_join_win *)
Definition pp_deads_P2_bv : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 22; 23; 25; 28; 29; 30; 31]%bv.
Definition pp_deads_PL_bv : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 26; 28; 29; 30; 31]%bv.
Definition pp_deads_P3_bv : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 22; 26; 28; 29; 30; 31]%bv.
Definition pp_deads_P4_bv : list (bv 5) :=
[1; 2; 5; 6; 7; 9; 10; 11; 12; 14; 15; 16; 17; 19; 21; 22; 23; 24; 25; 26; 28; 29; 30; 31]%bv.
(* [knock A/APgMain1.v:235-246, the donor's A/ACf1.v:267-281]: point register rr at a fresh atom a holding its
   current value v (Hv : v = U Ev e, Ea : ew _ a = Z_to_bv 64 v) *)
Ltac pin_reg HS rr a v Hv Ea :=
lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ssx) rr) in
remember (U Ev e) as v eqn:Hv;
let Q := fresh "Q" in
assert (Q : getr (ms_regs ms) rr = sv_denot Ev e) by exact (st_ok_restrict_reg tfibsegs Hh Ev ssx ms rr HS);
add_atom_win HS a (Z_to_bv 64 v) Ea;
lazymatch type of HS with st_ok _ ?Ev2 ?ssx2 ?msv2 =>
let HS3 := fresh "HS3" in
pose proof (st_ok_pin_rege Ev2 ssx2 msv2 rr (SOff a 0) HS ltac:(intros X; discriminate X)
ltac:(rewrite sv_denot_SOff0, Ea; cbn [ms_regs restrict mkst]; rewrite Q, Hv; symmetry; apply denot_lit_U)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end; clear Q end.
(* [knock A/APgMain3.v:63-75]: set register r to the expression e, dtac proving sv_denot Ev e = (the old value) *)
Ltac pin_by HS r e dtac :=
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
let eo := eval vm_compute in (sr_get (ss_regs ssx) r) in
let Hv := fresh "Hv" in
assert (Hv : sv_denot Ev e = sv_denot Ev eo) by dtac;
let HS3 := fresh "HS3" in
pose proof (st_ok_pin_rege Ev ssx msx r e HS ltac:(intros X; discriminate X)
(eq_trans Hv (eq_sym (st_ok_reg tfibsegs Ev ssx msx r HS)))) as HS3;
clear HS Hv; rename HS3 into HS; norm_ss HS end.
Ltac pin_tac :=
rewrite sv_denot_SOff0; cbn [sv_denot];
repeat match goal with H : ew ?Ex ?m = Z_to_bv 64 _ |- context [ew ?Ex ?m] => rewrite H end;
rewrite ?unsigned_lit_small by lia; first [reflexivity | f_equal; lia].
(* [knock A/APgMain4.v:120-127]: point register r at the atom n (Hn : ew Ev n = _), dtac proving the old
   expression has that value *)
Ltac pin_den HS r n Hn dtac :=
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msv =>
let HS3 := fresh "HS3" in
pose proof (st_ok_pin_rege Ev ssx msv r (SOff n 0) HS ltac:(intros X; discriminate X)
  ltac:(rewrite (st_ok_reg tfibsegs Ev ssx msv r HS); rewrite sv_denot_SOff0, Hn;
        lazymatch goal with |- _ = sv_denot _ ?e => let e' := eval vm_compute in e in change e with e' end;
        symmetry; dtac)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
(* add the fact f of atom n, ftac proving afact_ok Ev n f *)
Ltac add_fact HS n f ftac :=
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in
pose proof (st_ok_add_fact tfibsegs Ev ssx msx n f HS ltac:(ftac)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
(* [knock A/APgMain4.v:130-137]: give the atom n the fact f the state carries for atom m, vtac proving
   ew Ev m = ew Ev n *)
Ltac add_fact_of HS n f m vtac :=
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in let Hf := fresh "Hf" in let Hm := fresh "Hm" in
assert (Hf : afact_ok Ev n f) by
  (pose proof (pp_atoms_ok_In Ev _ m f (proj1 (st_ok_facts_ok tfibsegs Ev ssx msx HS))
     ltac:(vm_compute; repeat (first [left; reflexivity | right]))) as Hm;
   unfold afact_ok in Hm |- *; replace (ew Ev n) with (ew Ev m) by vtac; exact Hm);
pose proof (st_ok_add_fact tfibsegs Ev ssx msx n f HS Hf) as HS3; clear HS Hf; rename HS3 into HS; norm_ss HS end.
(* [knock A/APgLoop0.v:254-268 pl_run / pl_run_to / br_split, at PPBspan]: a run with the token runner and its
   write ranges, and the branch the engine cannot decide with its condition named Hc *)
Ltac pp_run HS HJ AG fpos F EFA octac :=
reshok HS;
lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ =>
aj_run_tok tfibtbl_lib_ok HS HJ SH PPBspan;
try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => ppAWR AG fpos F EFA octac end) end.
Ltac pp_run_to HS HJ AG fpos F EFA octac stop :=
reshok HS;
lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tok tfibtbl_lib_ok HS HJ SH PPBspan stop;
try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => ppAWR AG fpos F EFA octac end) end.
Ltac pp_br HS Hc :=
reshok HS;
lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok tfibtbl_lib_ok HS SH PPBspan end;
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
