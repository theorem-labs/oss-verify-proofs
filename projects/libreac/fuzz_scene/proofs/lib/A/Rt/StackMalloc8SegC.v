(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_scene (asan). Seg C of the __asan_stack_malloc_8
   walk: lib/A/Rt/StackMalloc8Cuts.v's `sm8_segC`, from the cut PC_SM8_FOUND to the jal into __asan::PoisonShadow.
   Ported from cgif_rgb_fuzzer lib/YF9c.v:32 (tra_stack_malloc7_at) in the shape fuzz_scene's own relocated
   class-1 walk states it (lib/A/AF0s.v, with lib/A/AF0r.v's tables), with class-8 constants. *)

(*   What the phase does (MEASURED, dis-__asan_stack_malloc_8-asan.txt; every pc below is PC_SM8_FOUND + an offset,
   no literal address appears in this file):
     +0x00 .. +0x10   hint cell [F + 8 * 8] := hint', flag byte [flag_addr ly 8 pos] := 1
     +0x14 .. +0x30   the frame address is built: s2 := F + kFakeFramesOff + 8 * 2^kStackSizeLog + pos * 2^14
     +0x34, +0x3c     [frame + 0x18] := s0 (the caller's sp) and [frame + fs_frame_bytes 8 - 8] := flag address
     +0x44            jal into the __asan::MemToShadow copy at PC_MEM_TO_SHADOW; the result is discarded
     +0x48 .. +0x54   a0 := frame, a1 := n, a2 := 0
     +0x54            jal into __asan::PoisonShadow at PC_POISON_SHADOW, ra := PC_SM8_MSRET
   The engine walks the phase in three runs: the first stops where the frame address first reaches a store
   (+0x34), because that address is not a region base; the second runs over the frame region to the MemToShadow
   entry; the third carries the four moves after the call. MemToShadow itself is NOT walked: it is the published
   summary `mem_to_shadow_realizes` of lib/Reusable/AsStackLeaf.v (a Theorem Labs lane owns that proof), taken as the
   hypothesis of the lemma below. The summary's use is isolated in ONE step of the proof (the `MTS` application),
   so a change of its shape touches nothing else here.

   WHERE AR IS CLOSED: astack_malloc_law_ok (lib/Reusable/YG0t.v:662) is applied at the end of the phase, before
   the MemToShadow call, over the memory that carries the four writes; sm8_midCD then carries `AR .. S' ..`.
   AR for Seg C's own input memory (mem2) comes from the entry's AR and sm8_midBC's raw memory clause, through
   al_frame of AR_laws. The reader-level clause alone cannot do it: ahs / ahz (YG0n.v:442-450) constrain raw bytes
   at band addresses that `aview` hides.

   The file itself names no A/AB01, A/AB03, A/AD2j, A/AD1k, A/AF0m (nor their Y twins), but its imports are not free
   of the staged start-up tables: A/AF0x.v (:17) and A/AE2y.v (:19), which it Requires, both Require A/AF0l.v and
   A/AF0m.v, so A/AF0m is in its Require closure (a Theorem Labs lane, SEG8-REVIEW.md section 14). No statement or premise
   of this file uses a name of A/AF0m. The phase reads no constant cell, so the file adds no start-up or
   constant-cell Section hypothesis. Its only hypotheses are `AR_laws` (the ambient laws every walk in this tree
   takes) and the MemToShadow summary. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0s YG0t.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import AB1v AE34 AF0x AE2y.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN32 YG0q YF0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Rt Require Import StackMalloc8Tbl StackMalloc8Cuts.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---------- the phase's code table and its two run lemmas ---------- *)
(* PC_SM8_FOUND .. PC_SM8_FOUND + 0x54, the 22 instructions of Seg C. Neither callee is in the table. *)
Definition sm8_ranges : list (Z * nat) := [(PC_SM8_FOUND, 22%nat)].
Definition tbl8 : ctable := Eval vm_compute in build_ranges sm8_ranges tbl_icpt.
Lemma tbl8_eq : tbl8 = build_ranges sm8_ranges tbl_icpt. Proof. vm_cast_no_check (eq_refl tbl8). Qed.
Lemma tbl8_ok : table_ok tfibsegs tbl8.
Proof. rewrite tbl8_eq. apply build_ranges_ok; [unfold sm8_ranges; repeat constructor; cbn; discriminate | exact tbl_icpt_ok]. Qed.
Lemma sm8_phase : forall (W : world tfibsegs) E ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_runN tfibsegs tbl8 FUEL ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1) | _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\ frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfibsegs tbl8 tbl8_ok AF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|]. split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Lemma sm8_phase_to : forall (W : world tfibsegs) E stop ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_run_toN tfibsegs tbl8 FUEL stop ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1) | _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\ frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E stop ss ss' st ms md HS Hrun.
eapply (SRr_run_to_gen tfibsegs tbl8 tbl8_ok AF0x.Hwx_tfa W FUEL stop E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|]. split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Definition RUNTO (stop : Z) (s : sstate) := sym_run_toN tfibsegs tbl8 FUEL stop s.
Definition RUN (s : sstate) := sym_runN tfibsegs tbl8 FUEL s.
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG ss r) v.

(* ---------- the class-8 frame geometry, by name ---------- *)
(* The hint cell of class 8 inside the fake stack, the frame size, and the two offsets the model's
   flag_addr / frame_addr reduce to for cid = 8. *)
Definition HOFF : Z := 8 * CID8.
Definition FB : Z := fs_frame_bytes CID8.
Definition FLOFF8 : Z := kFakeFlagsOff + fs_flags_off CID8.
Definition FROFF8 : Z := kFakeFramesOff + CID8 * Z.shiftl 1 kStackSizeLog.
Lemma flag_addr_cid8 : forall ly pos, flag_addr ly CID8 pos = ly_F ly + FLOFF8 + pos.
Proof. intros ly pos. unfold flag_addr, fs_flag_off, FLOFF8. lia. Qed.
Lemma frame_addr_cid8 : forall ly pos, frame_addr ly CID8 pos = ly_F ly + FROFF8 + pos * FB.
Proof. intros ly pos. unfold frame_addr, fs_frame_off, FROFF8, FB. lia. Qed.
Lemma FLOFF8_eq : FLOFF8 = 36736. Proof. vm_compute. reflexivity. Qed.
Lemma FROFF8_eq : FROFF8 = 8425472. Proof. vm_compute. reflexivity. Qed.
Lemma FB_eq : FB = 16384. Proof. vm_compute. reflexivity. Qed.
Lemma HOFF_eq : HOFF = 64. Proof. vm_compute. reflexivity. Qed.
Lemma fs_frames_cid8 : fs_frames CID8 = 64. Proof. vm_compute. reflexivity. Qed.

(* ---------- the three symbolic phases ---------- *)
(* The registers at the cut: every register is its own atom, except s3, which sm8_midBC pins to the literal
   kStackSizeLog (the walk shifts by it, so the engine needs the literal). *)
Definition aFF : nat := 32%nat.
Definition rF : YP09.region := YP09.mkRegion (Some 18%nat) HOFF (HOFF + 8) HOFF (HOFF + 8) [].
Definition rFLG : YP09.region := YP09.mkRegion (Some 13%nat) 0 1 0 1 [].
Definition rFF : YP09.region := YP09.mkRegion (Some aFF) 0 FB 0 FB [].
Definition regsC : list sv := Eval vm_compute in (firstn 19 sr_atoms ++ [SLit kStackSizeLog] ++ skipn 20 sr_atoms).
Definition factsC : list (nat * afact) :=
[(18%nat, mkAF 4096 (CEIL_MAX - kFakeStackSize) 12);
(11%nat, mkAF 4096 CEIL_MAX 0);
(13%nat, mkAF 4096 CEIL_MAX 0);
(17%nat, mkAF 0 (fs_frames CID8 - 1) 0)].
Definition ssC1 : sstate := mkSS PC_SM8_FOUND regsC [rF; rFLG] None (mkFacts factsC [] []).
Definition eC1 : sstate := Eval vm_compute in fst (RUN ssC1).
Definition stC1 : run_status := Eval vm_compute in snd (RUN ssC1).
Lemma r_C1 : RUN ssC1 = (eC1, stC1). Proof. vm_cast_no_check (eq_refl (RUN ssC1)). Qed.
Definition s2C1 : sv := Eval vm_compute in RG eC1 18.
Definition add_fact (ss : sstate) (n : nat) (f : afact) : sstate :=
mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss)
(mkFacts ((n, f) :: f_atoms (ss_facts ss)) (f_conds (ss_facts ss)) (f_alias (ss_facts ss))).
Lemma st_ok_add_fact : forall E ss ms n lo hi,
st_ok tfibsegs E ss ms -> ss_resv ss = None -> lo <= bv_unsigned (ew E n) <= hi ->
st_ok tfibsegs E (add_fact ss n (mkAF lo hi 0)) ms.
Proof.
intros E ss ms n lo hi HS Hrv Hr.
destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & (HA & HC & HL)).
unfold st_ok, add_fact. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts f_atoms f_conds f_alias].
rewrite Hrv in H4 |- *.
repeat (split; [assumption|]). split; [|split; assumption].
cbn [atoms_ok]. split; [|exact HA]. unfold afact_ok. cbn [af_lo af_hi af_al2].
split; [exact Hr|]. split; [rewrite Z.pow_0_r; apply Z.mod_1_r | lia].
Qed.
Definition memC2 : smem := rFF :: ss_mem eC1.
Definition preC2 : sstate :=
add_fact (mkSS (ss_pc eC1) (sr_sets (ss_regs eC1) [((18%bv : bv 5), SOff aFF 0)]) memC2 None (ss_facts eC1))
aFF (mkAF 4096 (CEIL_MAX - FB) 0).
Definition ssC2 : sstate := Eval vm_compute in preC2.
Lemma ssC2_eq : preC2 = ssC2. Proof. vm_compute. reflexivity. Qed.
Definition eC2 : sstate := Eval vm_compute in fst (RUNTO PC_MEM_TO_SHADOW ssC2).
Definition stC2 : run_status := Eval vm_compute in snd (RUNTO PC_MEM_TO_SHADOW ssC2).
Lemma r_C2 : RUNTO PC_MEM_TO_SHADOW ssC2 = (eC2, stC2). Proof. vm_cast_no_check (eq_refl (RUNTO PC_MEM_TO_SHADOW ssC2)). Qed.
(* The pc MemToShadow returns to: the jal's own pc plus 4. *)
Definition PC_SM8_MTSRET : Z := PC_SM8_FOUND + 0x48.
Definition ssC3 : sstate := mkSS PC_SM8_MTSRET sr_atoms [] None (mkFacts [] [] []).
Definition eC3 : sstate := Eval vm_compute in fst (RUNTO PC_POISON_SHADOW ssC3).
Definition stC3 : run_status := Eval vm_compute in snd (RUNTO PC_POISON_SHADOW ssC3).
Lemma r_C3 : RUNTO PC_POISON_SHADOW ssC3 = (eC3, stC3). Proof. vm_cast_no_check (eq_refl (RUNTO PC_POISON_SHADOW ssC3)). Qed.

(* What the three runs leave, all MEASURED by the engine (vm_compute). *)
Lemma C1_facts : ss_pc eC1 = PC_SM8_FOUND + 0x34 /\ reg_is eC1 18 s2C1 = true /\ ss_atoms_lt 32 eC1 = true /\ ss_resv eC1 = None /\
match stC1 with RS_stopped (SR_addr _) => True | _ => False end.
Proof. vm_compute. repeat split; reflexivity || exact I. Qed.
Lemma stC1_match : forall (A : Type) (x y : A), match stC1 with RS_ecall => x | _ => y end = y. Proof. intros A x y. reflexivity. Qed.
Lemma stC2_match : forall (A : Type) (x y : A), match stC2 with RS_ecall => x | _ => y end = y. Proof. intros A x y. reflexivity. Qed.
Lemma stC3_match : forall (A : Type) (x y : A), match stC3 with RS_ecall => x | _ => y end = y. Proof. intros A x y. reflexivity. Qed.
(* The frame offset the walk adds to a1 = F + kFakeFlagsOff, i.e. the frames' area seen from the flags' area. *)
Definition FROFF8_FROM_FLAGS : Z := FROFF8 - kFakeFlagsOff.
Lemma FROFF8_FROM_FLAGS_eq : FROFF8_FROM_FLAGS = 8421376. Proof. vm_compute. reflexivity. Qed.
Lemma s2C1_eq : s2C1 = SAlu ALU_ADD (SOff 11%nat FROFF8_FROM_FLAGS) (SAlu ALU_SLL (SOff 17%nat 0) (SLit 14)).
Proof. vm_compute. reflexivity. Qed.
Lemma s2C1_denot : forall E F pos, bv_unsigned (ew E 11%nat) = F + kFakeFlagsOff -> bv_unsigned (ew E 17%nat) = pos ->
0 <= F -> 0 <= pos -> F + FROFF8 + pos * FB < 2 ^ 64 -> sv_denot E s2C1 = Z_to_bv 64 (F + FROFF8 + pos * FB).
Proof.
intros E F pos HF Hp HF0 Hp0 Hhi. rewrite FROFF8_eq, FB_eq in Hhi |- *.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E s2C1)). f_equal.
change (bv_unsigned (sv_denot E s2C1)) with (U E s2C1). rewrite (U_zev E s2C1) by (vm_compute; reflexivity).
rewrite s2C1_eq, FROFF8_FROM_FLAGS_eq. cbn [zev zalu_raw]. unfold rho_of. rewrite HF, Hp, Z.add_0_r.
unfold kFakeFlagsOff. change (Z.land (zcanon 14) 63) with 14.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 14) with 16384.
rewrite (zcanon_small pos) by lia. rewrite (zcanon_small (pos * 16384)) by lia.
rewrite (zcanon_small (F + 4096 + 8421376)) by lia.
replace (F + 4096 + 8421376 + pos * 16384) with (F + 8425472 + pos * 16384) by lia.
apply zcanon_small. lia.
Qed.
Lemma C2_facts : ss_pc eC2 = PC_MEM_TO_SHADOW /\ ss_resv eC2 = None /\ ss_atoms_lt 33 eC2 = true /\
reg_is eC2 1 (SLit PC_SM8_MTSRET) = true /\ reg_is eC2 10 (SOff aFF 0) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma C3_facts : ss_pc eC3 = PC_POISON_SHADOW /\ ss_resv eC3 = None /\ ss_mem eC3 = [] /\
reg_is eC3 1 (SLit PC_SM8_MSRET) = true /\ reg_is eC3 10 (SOff 18%nat 0) = true /\
reg_is eC3 11 (SOff 9%nat 0) = true /\ reg_is eC3 12 (SLit 0) = true /\
forallb (fun r => reg_is eC3 r (SOff (Z.to_nat r) 0)) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* The regions at the end of the second run: the frame, the hint cell and the flag byte, with the four writes. *)
Definition rFF2 : YP09.region := Eval vm_compute in nth 0 (ss_mem eC2) rFF.
Definition rF2 : YP09.region := Eval vm_compute in nth 1 (ss_mem eC2) rFF.
Definition rFLG2 : YP09.region := Eval vm_compute in nth 2 (ss_mem eC2) rFF.
Lemma eC2_regions : nth_error (ss_mem eC2) 0 = Some rFF2 /\ nth_error (ss_mem eC2) 1 = Some rF2 /\ nth_error (ss_mem eC2) 2 = Some rFLG2.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma rFF2_shape : YP09.r_base rFF2 = Some aFF /\ YP09.r_wlo rFF2 = 0 /\ YP09.r_whi rFF2 = FB /\
nth_error (YP09.r_chunks rFF2) 0 = Some (YP09.mkChunk 16376 (CVal 8 (SOff 13%nat 0))).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma rF2_shape : YP09.r_base rF2 = Some 18%nat /\ YP09.r_wlo rF2 = HOFF /\ YP09.r_whi rF2 = HOFF + 8 /\
nth_error (YP09.r_chunks rF2) 0 = Some (YP09.mkChunk 64 (CVal 8 (SOff 12%nat 1))).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma rFLG2_shape : YP09.r_base rFLG2 = Some 13%nat /\ YP09.r_wlo rFLG2 = 0 /\ YP09.r_whi rFLG2 = 1 /\
nth_error (YP09.r_chunks rFLG2) 0 = Some (YP09.mkChunk 0 (CVal 1 (SLit 1))).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma memC1_windows : forall E a, in_wrange E (ss_mem ssC1) a ->
(bv_unsigned (ew E 18%nat) + HOFF <= a < bv_unsigned (ew E 18%nat) + (HOFF + 8)) \/
(bv_unsigned (ew E 13%nat) + 0 <= a < bv_unsigned (ew E 13%nat) + 1).
Proof.
intros E a Hin. destruct (in_wrange_windows E _ _ Hin) as (b & lo & hi & Ht & Hw).
vm_compute in Ht. repeat (destruct Ht as [Hq | Ht]; [injection Hq as <- <- <-; cbn [base_val] in Hw; first [left; exact Hw | right; exact Hw | exfalso; lia] |]). destruct Ht.
Qed.
Lemma memC2_windows : forall E a, in_wrange E (ss_mem ssC2) a ->
(bv_unsigned (ew E aFF) + 0 <= a < bv_unsigned (ew E aFF) + FB) \/
(bv_unsigned (ew E 18%nat) + HOFF <= a < bv_unsigned (ew E 18%nat) + (HOFF + 8)) \/
(bv_unsigned (ew E 13%nat) + 0 <= a < bv_unsigned (ew E 13%nat) + 1).
Proof.
intros E a Hin. destruct (in_wrange_windows E _ _ Hin) as (b & lo & hi & Ht & Hw).
vm_compute in Ht. repeat (destruct Ht as [Hq | Ht]; [injection Hq as <- <- <-; cbn [base_val] in Hw;
first [left; exact Hw | right; left; exact Hw | right; right; exact Hw | exfalso; lia] |]). destruct Ht.
Qed.

(* ---------- small generic facts (copies of lib/A/AF0r.v's, which this file must not import) ---------- *)
Lemma stack_malloc_inv : forall cid S pos S',
apath (stack_malloc cid S) [] (PFake cid pos, S') ->
exists hint', fs_probe (Z.to_nat (fs_frames cid)) (fs_live (st_fs S)) cid (znth 0 cid (fs_hint (st_fs S))) = Some (pos, hint') /\
S' = set_fs (mkFS (zupd cid hint' (fs_hint (st_fs S))) ((cid, pos) :: fs_live (st_fs S))) S.
Proof.
intros cid S pos S' H. unfold stack_malloc, bind, get, put, ret in H. cbn [ibind] in H.
destruct (fs_probe (Z.to_nat (fs_frames cid)) (fs_live (st_fs S)) cid (znth 0 cid (fs_hint (st_fs S)))) as [[p h']|] eqn:Hp.
- cbn [ibind apath] in H. injection H as <- <-. exists h'. split; reflexivity.
- cbn [apath] in H. discriminate H.
Qed.
Lemma fs_probe_facts : forall fuel live cid h pos hint',
fs_probe fuel live cid h = Some (pos, hint') -> 0 < fs_frames cid ->
mem_pos live cid pos = false /\ 0 <= pos < fs_frames cid /\ h < hint' /\ pos = (hint' - 1) mod fs_frames cid.
Proof.
induction fuel as [|f IH]; intros live cid h pos hint' Hp HN; [discriminate Hp|].
cbn [fs_probe] in Hp. destruct (mem_pos live cid (h mod fs_frames cid)) eqn:Hm.
- destruct (IH _ _ _ _ _ Hp HN) as (A & Bq & C & D). repeat split; first [assumption | lia].
- injection Hp as <- <-. pose proof (Z.mod_pos_bound h (fs_frames cid) HN). replace (h + 1 - 1) with h by lia. repeat split; first [exact Hm | lia].
Qed.
Lemma env_agree_Ereg_app : forall regs l1 l2 k, (k <= 32 + length l1)%nat -> env_agree k (Ereg regs l1) (Ereg regs (l1 ++ l2)).
Proof.
intros regs l1 l2 k Hk. split; [|reflexivity]. intros n Hn.
destruct (Nat.lt_ge_cases n 32) as [L|L].
- unfold Ereg. cbn [ew]. destruct (n <? 32)%nat eqn:E; [reflexivity | apply Nat.ltb_ge in E; lia].
- replace n with (32 + (n - 32))%nat by lia. rewrite !ew_Ereg_extra. rewrite app_nth1 by lia. reflexivity.
Qed.
Lemma aview_of_val_mem : forall (H : word -> bool) mem a (n : nat) v k, val_mem tfibsegs (mrestrict H mem) a n v -> (k < n)%nat ->
aview tfibsegs H mem (a + Z.of_nat k) = Some (YG0f.le_byte v n k).
Proof.
intros H mem a n v k Hv Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned. change (YG0f.le_byte v n k) with (YO0f.le_byte v n k).
unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
Lemma hs_kept_gen : forall (H : word -> bool) (mem mem' : word -> option byte) (P : Z -> Prop),
(forall z : word, ~ P (bv_unsigned z) -> mem' z = mem z) ->
(forall a, P a -> exists m0, apresent H m0 a) ->
forall a, in_band_rw a -> H (Z_to_bv 64 a) = true -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof.
intros H mem mem' P MEQ PRES a Ha Hh. rewrite MEQ; [reflexivity|]. intros HP.
rewrite unsigned_lit_small in HP by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; lia).
destruct (PRES a HP) as (m0 & Hf & _). rewrite Hh in Hf. discriminate Hf.
Qed.
Lemma rdword_ext : forall (rd rd' : reader) a,
(forall k, 0 <= k < 8 -> rd' (a + k) = rd (a + k)) -> rdword rd' a = rdword rd a.
Proof.
intros rd rd' a Hk. unfold rdword.
replace (rd' a) with (rd a) by (rewrite <- (Z.add_0_r a); symmetry; apply Hk; lia).
rewrite !Hk by lia. reflexivity.
Qed.

(* ---------- Seg C ---------- *)
Section f.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.

Lemma sm8_segC_holds : mem_to_shadow_realizes tfibsegs B PC_MEM_TO_SHADOW -> sm8_segC B.
Proof.
intros MTS ly S W regs mem md pos S' n hint' regs2 mem2 md2 HE HM2.
pose proof HE as (HPRE & G10n & Hnq & Hnq8 & Hcnt & Hpath).
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp). unfold ESTACK in Hslo, HpresE.
pose proof HM2 as (Hprobe2 & R12 & R17 & R13 & R2 & R8 & R9 & R18 & R19 & R11 & Hkept2 & Hsaved2 & Hraw2 & Hpres2 & Hmd2).
unfold sm8_midCD, sm8_regs_kept, sm8_saved, sm8_stack_pres, sm8_mem_kept in *.
pose proof AF0x.Hwx_tfa as Hwx.
destruct (stack_malloc_inv CID8 S pos S' Hpath) as (h2 & Hprobe & HS'eq).
assert (Eh2 : h2 = hint') by congruence. subst h2. clear Hprobe.
set (hints := fs_hint (st_fs S)) in *. set (live := fs_live (st_fs S)) in *. set (hint := znth 0 CID8 hints) in *.
destruct (fs_probe_facts _ _ _ _ _ _ Hprobe2 ltac:(rewrite fs_frames_cid8; lia)) as (Hfree & Hposr & Hhh & Hposeq).
rewrite fs_frames_cid8 in Hposr.
pose proof (proj1 HAR) as M.
pose proof (am_layout B ly S _ M) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
pose proof (img_cover_of_ledger ly _ _ (proj1 (proj2 HAR))) as IMG.
assert (ZI : forall e, In e (owned_extents ly) -> zone3 (fst e) (snd e)).
{ intros e Hex. pose proof (proj1 (Forall_forall _ _) (lo_app ly HLY) e Hex) as IA. cbv beta in IA.
assert (D9 : zdisjoint e (ly_img ly)).
{ pose proof (lo_disj ly HLY) as PD.
exact (pairwise_In zdisjoint (static_extents ly) e (ly_img ly) (owned_extents ly ++ [(ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)]) [ly_img ly]
ltac:(unfold static_extents; rewrite <- app_assoc; reflexivity) PD ltac:(apply in_app_iff; left; exact Hex) ltac:(left; reflexivity)). }
assert (SZ : 0 <= snd e).
{ unfold owned_extents in Hex. cbn [In] in Hex. decompose [or] Hex; subst; cbn [snd];
unfold kPrimResvSize, kPtrArrayResv, kThreadObjSize, kFakeStackSize, kNodesBlockSize, kStoreBlockSize; lia. }
exact (zone3_intro ly (fst e) (snd e) IMG SZ IA ltac:(destruct e; exact D9)). }
pose proof (ZI (ly_F ly, kFakeStackSize) ltac:(unfold owned_extents; cbn; tauto)) as (HF1 & HF2 & HFz).
cbn [fst snd] in HF1, HF2, HFz.
ceil; unfold ASAN_CEIL, kFakeStackSize in HF1, HF2.
unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kFakeStackSize in HFz.
assert (ZONE : exists hi : bool, if hi then 17594333495296 <= ly_F ly /\ ly_F ly + 11571200 <= alloc_ceiling else 6262784 <= ly_F ly /\ ly_F ly + 11571200 <= 2147446784).
{ destruct HFz as [X|[X|X]]; [exfalso; clear - X HF1; lia | exists false; exact X | exists true; exact X]. }
destruct ZONE as [hi HZ].
clear HF1 HF2. assert (HF1 : 6262784 <= ly_F ly) by (clear - HZ; destruct hi; lia).
assert (HF2 : ly_F ly + 11571200 <= 140737479966720) by (clear - HZ; destruct hi; [ceil; lia | lia]).
assert (CE : alloc_ceiling <= 140737479966720) by (ceil; lia).
pose proof (lo_F_al ly HLY) as HFal. unfold page_aligned in HFal.
pose proof (lo_disj ly HLY) as PW. unfold static_extents, owned_extents in PW. cbn [app pairwise] in PW.
destruct PW as (_ & _ & _ & PWF & _).
assert (DFS : zdisjoint (ly_F ly, kFakeStackSize) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)) by (exact (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail PWF)))))).
clear PWF. unfold zdisjoint, kFakeStackSize in DFS. cbn [fst snd] in DFS.
set (F := ly_F ly) in *. set (sp0 := spZ regs) in *. set (H := w_H W) in *.
unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
assert (Hsp44 : 2 ^ 44 <= sp0 <= 2 ^ 47) by (clear - Hslo Htop Lbeg Lhi; lia).
set (FLG := flag_addr ly CID8 pos) in *. set (FF := frame_addr ly CID8 pos) in *.
assert (HFLG : FLG = F + 36736 + pos) by (subst FLG; rewrite flag_addr_cid8, FLOFF8_eq; reflexivity).
assert (HFF : FF = F + 8425472 + pos * 16384) by (subst FF; rewrite frame_addr_cid8, FROFF8_eq, FB_eq; reflexivity).
assert (HF8m : F mod 8 = 0) by (apply Z.mod_divide; [lia|]; exists (F / 4096 * 512); pose proof (Z.div_mod F 4096 ltac:(lia)); lia).
pose proof (Z.div_mod F 8 ltac:(lia)) as HF8. rewrite HF8m, Z.add_0_r in HF8.
(* the shadow of the frame, and where it sits relative to the fake stack and the caller's stack *)
assert (HFFd : FF / 8 = F / 8 + 1053184 + pos * 2048).
{ rewrite HFF. replace (F + 8425472 + pos * 16384) with ((F / 8 + 1053184 + pos * 2048) * 8) by (clear - HF8; lia).
rewrite Z_div_mult by lia. reflexivity. }
assert (HSH : shadow_addr FF = 2147450880 + F / 8 + 1053184 + pos * 2048).
{ unfold shadow_addr, SHADOW_OFF. rewrite HFFd. lia. }
assert (HSHF : 2147450880 + F / 8 + 1053184 + pos * 2048 + 2048 <= F \/
F + 11571200 <= 2147450880 + F / 8 + 1053184 + pos * 2048).
{ clear - hi HZ HF8 Hposr. destruct hi; [left | right]; lia. }
(* the fake stack and the shadow of its frames are present in the caller's memory *)
assert (INA : forall x l1 l2 l3 (l4 : list (aexp * Z)), In x l4 -> In x (l1 ++ l2 ++ l3 ++ l4)) by (intros; rewrite !in_app_iff; tauto).
assert (PRF : forall a, F <= a < F + kFakeStackSize -> apresent H mem a).
{ intros a Ha. pose proof (proj1 (Forall_forall _ _) (am_areas B ly S _ M) (AF 0, kFakeStackSize) ltac:(unfold aareas; apply INA; left; reflexivity)) as V.
specialize (V (a - F) ltac:(cbn [snd]; clear - Ha; lia)). cbn [fst aeval] in V. replace (ly_F ly + 0 + (a - F)) with a in V by (subst F; lia).
destruct (mbyte tfibsegs (mrestrict H mem) a) as [b|] eqn:Hb; [| exfalso; apply V; unfold aview; rewrite Hb; reflexivity].
eapply (AF0x.mbyte_high_apresent H mem a); [clear - Ha HF1 HF2; unfold TFIB_IMG_END, kFakeStackSize in *; lia | exact Hb]. }
assert (PRS : forall a, shadow_addr (F + kFakeFramesOff) <= a < shadow_addr (F + kFakeFramesOff) + 1441792 -> apresent H mem a).
{ intros a Ha. pose proof (proj1 (Forall_forall _ _) (am_areas B ly S _ M) (ASh (AF kFakeFramesOff), (kFakeStackSize - kFakeFramesOff) / 8) ltac:(unfold aareas; apply INA; do 5 right; left; reflexivity)) as V.
change ((kFakeStackSize - kFakeFramesOff) / 8) with 1441792 in V.
specialize (V (a - shadow_addr (F + kFakeFramesOff)) ltac:(cbn [snd]; clear - Ha; lia)). cbn [fst aeval] in V.
replace (shadow_addr (ly_F ly + kFakeFramesOff) + (a - shadow_addr (F + kFakeFramesOff))) with a in V by (subst F; lia).
destruct (mbyte tfibsegs (mrestrict H mem) a) as [b|] eqn:Hb; [| exfalso; apply V; unfold aview; rewrite Hb; reflexivity].
unfold shadow_addr, kFakeFramesOff, SHADOW_OFF in Ha. replace ((F + (4096 + 32768)) / 8) with (F / 8 + 4608) in Ha by (replace (F + (4096 + 32768)) with ((F / 8 + 4608) * 8) by (clear - HF8; lia); rewrite Z_div_mult by lia; reflexivity).
eapply (AF0x.mbyte_high_apresent H mem a); [clear - Ha HF1 HF2 HF8; unfold TFIB_IMG_END, kFakeStackSize in *; lia | exact Hb]. }
clear INA.
(* ---- AR for Seg C's own input memory: only the caller's stack window may differ ---- *)
assert (RAW2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - SM8_WIN <= a < sp0) -> mem2 (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
{ intros a Ha Hn. apply Hraw2. rewrite unsigned_lit_small by exact Ha. exact Hn. }
assert (OWNSTK : forall a, aowned B ly S a -> ~ (sp0 - SM8_WIN <= a < sp0)).
{ intros a Hown Hs. exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(clear - Hs Hslo Htop; unfold SM8_WIN in *; lia) Hown). }
assert (OWNLOW : forall a, aowned B ly S a -> 0 <= a < 2 ^ 64).
{ intros a Hown. pose proof (al_owned_low _ _ LAWS ly S W mem md a HAR Hown). ceil. unfold ASAN_CEIL in *. lia. }
assert (HAR2 : AR tfibsegs B ly S W mem2 md2).
{ pose proof (same_but_materialized_frame md md2 Hmd2) as MF2.
apply (al_frame _ _ LAWS ly S W mem md mem2 md2 HAR).
all: change (w_H W) with H.
- intros a Ha Hown. apply aview_same. apply RAW2; [exact Ha | exact (OWNSTK a Hown)].
- intros a Hv. rewrite (AE2y.aview_mod _ mem2 a). rewrite (AE2y.aview_mod _ mem a) in Hv.
pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Hr. set (a' := a mod 2 ^ 64) in *. clearbody a'.
destruct (Z_lt_le_dec a' (sp0 - SM8_WIN)) as [L1|L1].
+ rewrite (aview_same H mem mem2 a' (RAW2 a' Hr ltac:(lia))). exact Hv.
+ destruct (Z_lt_le_dec a' sp0) as [L2|L2].
* apply AE2y.aview_some_of_apresent. apply Hpres2. unfold ESTACK, SM8_WIN in *. lia.
* rewrite (aview_same H mem mem2 a' (RAW2 a' Hr ltac:(lia))). exact Hv.
- apply MF2. - apply MF2. - apply MF2.
- intros a Ha Hh. apply Hraw2. rewrite unsigned_lit_small
by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; lia).
clear - Ha Hslo Lbeg. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, ESTACK, SM8_WIN in *. lia. }
(* ---- phase 1: the hint cell and the flag byte ---- *)
set (E := Ereg regs2 (@nil word)) in *.
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs2 r) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (U18 : bv_unsigned (ew E 18%nat) = F) by (rewrite (EEreg 18%nat 18%bv eq_refl), R18; apply unsigned_lit_small; unfold kFakeStackSize in *; lia).
assert (U11 : bv_unsigned (ew E 11%nat) = F + kFakeFlagsOff) by (rewrite (EEreg 11%nat 11%bv eq_refl), R11; apply unsigned_lit_small; unfold kFakeStackSize, kFakeFlagsOff in *; lia).
assert (U13 : bv_unsigned (ew E 13%nat) = FLG) by (rewrite (EEreg 13%nat 13%bv eq_refl), R13; apply unsigned_lit_small; unfold kFakeStackSize in *; lia).
assert (U17 : bv_unsigned (ew E 17%nat) = pos) by (rewrite (EEreg 17%nat 17%bv eq_refl), R17; apply unsigned_lit_small; lia).
assert (U12 : bv_unsigned (ew E 12%nat) = (hint' - 1) mod 2 ^ 64) by (rewrite (EEreg 12%nat 12%bv eq_refl), R12; unfold w64; rewrite Z_to_bv_unsigned; reflexivity).
assert (U8 : bv_unsigned (ew E 8%nat) = sp0) by (rewrite (EEreg 8%nat 8%bv eq_refl), R8; apply unsigned_lit_small; clear - Hsp44; lia).
assert (DEN0 : forall k z, bv_unsigned (ew E k) = z -> 0 <= z < 2 ^ 64 -> sv_denot E (SOff k 0) = Z_to_bv 64 z).
{ intros k z Hk Hr. cbn [sv_denot]. rewrite Hk, Z.add_0_r. reflexivity. }
assert (PRF2 : forall a, F <= a < F + kFakeStackSize -> apresent H mem2 a).
{ intros a Ha. apply (apresent_same H mem); [apply RAW2; [clear - Ha HF1 HF2; unfold kFakeStackSize in *; lia | clear - Ha DFS Hslo Htop; unfold SM8_WIN, ESTACK, kFakeStackSize in *; lia] | apply PRF; exact Ha]. }
assert (HSC1 : st_ok tfibsegs E ssC1 (restrict H (mkst regs2 (Z_to_bv 64 PC_SM8_FOUND) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssC1.
apply (st_ok_regs tfibsegs E (mkSS PC_SM8_FOUND sr_atoms [rF; rFLG] None (mkFacts factsC [] [])) _ regsC).
2:{ apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; rewrite (EEreg 19%nat 19%bv eq_refl), R19; reflexivity) ] |]).
destruct Hr. }
apply (entry_st_ok_full tfibsegs); change (Ereg regs2 (@nil word)) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
+ unfold rF, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U18.
split; [rewrite ?HOFF_eq; lia|]. split; [rewrite ?HOFF_eq; lia|]. split; [|apply Forall_nil].
intros o Ho. rewrite ?HOFF_eq in Ho. apply (AF0x.apresent_writable H); [unfold TFIB_IMG_END; clear - Ho HF1 HF2; lia|].
apply PRF2. unfold kFakeStackSize. lia.
+ unfold rFLG, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U13.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
intros o Ho. apply (AF0x.apresent_writable H); [unfold TFIB_IMG_END; clear - Ho HFLG HF1 HF2 Hposr; lia|].
apply PRF2. unfold kFakeStackSize. clear - Ho HFLG Hposr. lia.
- apply pairwise_disjoint_of_extents. unfold rF, rFLG, extent_of_region.
cbn [map fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U18, U13.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
rewrite ?HOFF_eq. clear - HFLG Hposr HF1 HF2. repeat split; lia.
- split; [|split; exact I]. unfold factsC. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite U18, U11, U13, U17, fs_frames_cid8. unfold kFakeFlagsOff.
change (2 ^ 12) with 4096. change (2 ^ 0) with 1.
repeat split; first [exact HFal | apply Z.mod_1_r | clear - HF1 HF2 HFLG Hposr HFal CE; unfold kFakeStackSize in *; lia]. }
eapply SRr_bind; [apply (sm8_phase W E ssC1 _ _ _ _ HSC1 r_C1)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HFm1 & HFrm1). rewrite ?wvb_wvb in *. rewrite stC1_match in HS1.
assert (MEQ1 : forall z : word, ~ (F + 64 <= bv_unsigned z < F + 64 + 8) -> bv_unsigned z <> FLG -> ms_mem ms1 z = mem2 z).
{ intros z Hz1 Hz2. apply HFm1. intros Hin. destruct (memC1_windows E _ Hin) as [Hw|Hw];
[rewrite U18 in Hw; rewrite ?HOFF_eq in Hw; lia | rewrite U13 in Hw; lia]. }
clear HFm1 HFrm1.
pose proof C1_facts as (PC1 & R18C1 & AT1 & RV1 & _).
pose proof (st_ok_restrict_mkst tfibsegs H E _ _ HS1 RV1) as Hshape1. rewrite PC1 in Hshape1. rewrite Hshape1. rewrite Hshape1 in HS1. clear Hshape1.
assert (RD1 : forall (r : bv 5) v, reg_is eC1 (bv_unsigned r) v = true -> getr (ms_regs ms1) r = sv_denot E v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr.
apply (st_ok_reg_denot H E eC1 (mkst (ms_regs ms1) (Z_to_bv 64 (PC_SM8_FOUND + 0x34)) (ms_mem ms1) (seg_rom tfibsegs)) r HS1). }
pose proof (RD1 18%bv s2C1 R18C1) as G18.
rewrite (s2C1_denot E F pos U11 U17 ltac:(lia) ltac:(lia) ltac:(rewrite FROFF8_eq, FB_eq; clear - HF1 HF2 Hposr; lia)) in G18.
replace (F + FROFF8 + pos * FB) with FF in G18 by (rewrite HFF, FROFF8_eq, FB_eq; reflexivity).
rewrite restrict_mkst_fx in HS1.
(* ---- phase 2: the two frame writes, up to the MemToShadow entry ---- *)
set (EC := Ereg regs2 [w64 FF]) in *.
assert (AGR : env_agree 32 E EC).
{ subst E EC. apply (env_agree_Ereg_app regs2 (@nil word) [w64 FF] 32). cbn. lia. }
assert (ECreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EC i = getr regs2 r) by (intros; subst EC; apply ew_Ereg_nat; assumption).
assert (HFFb : 4096 <= FF /\ FF + 16384 <= F + 11571200) by (rewrite HFF; clear - HF1 Hposr; lia).
assert (VFF : bv_unsigned (ew EC aFF) = FF).
{ subst EC. unfold aFF. rewrite (ew_Ereg_extra regs2 _ 0). cbn [nth]. apply unsigned_lit_small. clear - HFFb HF1 HF2 CE; lia. }
assert (V18 : bv_unsigned (ew EC 18%nat) = F) by (rewrite (ECreg 18%nat 18%bv eq_refl), R18; apply unsigned_lit_small; unfold kFakeStackSize in *; lia).
assert (V13 : bv_unsigned (ew EC 13%nat) = FLG) by (rewrite (ECreg 13%nat 13%bv eq_refl), R13; apply unsigned_lit_small; unfold kFakeStackSize in *; lia).
assert (V12 : bv_unsigned (ew EC 12%nat) = (hint' - 1) mod 2 ^ 64) by (rewrite (ECreg 12%nat 12%bv eq_refl), R12; unfold w64; rewrite Z_to_bv_unsigned; reflexivity).
assert (V8 : bv_unsigned (ew EC 8%nat) = sp0) by (rewrite (ECreg 8%nat 8%bv eq_refl), R8; apply unsigned_lit_small; clear - Hsp44; lia).
assert (DC0 : forall k z, bv_unsigned (ew EC k) = z -> 0 <= z < 2 ^ 64 -> sv_denot EC (SOff k 0) = Z_to_bv 64 z).
{ intros k z Hk Hr. cbn [sv_denot]. rewrite Hk, Z.add_0_r. reflexivity. }
assert (HSC2 : st_ok tfibsegs EC ssC2 (restrict H (mkst (ms_regs ms1) (Z_to_bv 64 (PC_SM8_FOUND + 0x34)) (ms_mem ms1) (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx, <- ssC2_eq. unfold preC2. rewrite PC1.
apply st_ok_add_fact; [| reflexivity | rewrite VFF; rewrite ?FB_eq; clear - HFFb HF1 HF2 CE; lia].
apply (st_ok_set_regs_mem tfibsegs 32 E EC eC1 (ms_regs ms1) (ms_regs ms1) (Z_to_bv 64 (PC_SM8_FOUND + 0x34)) (PC_SM8_FOUND + 0x34)
(mrestrict H (ms_mem ms1)) (mrestrict H (ms_mem ms1)) memC2 [((18%bv : bv 5), SOff aFF 0)] HS1 AGR AT1).
- vm_compute. reflexivity.
- intros r Hr. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. split; [reflexivity|]. rewrite G18. symmetry. apply (DC0 _ FF VFF).
clear - HFFb HF1 HF2 CE; lia.
- pose proof (st_ok_mem_ok tfibsegs EC eC1 _ (st_ok_agree tfibsegs 32 E EC eC1 _ HS1 AGR AT1)) as (WF1 & ROK1 & PD1).
split; [vm_compute; reflexivity|]. split.
+ unfold memC2. apply Forall_cons; [|exact ROK1].
unfold rFF, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite VFF.
split; [rewrite ?FB_eq; clear - HFFb HF1 HF2 CE; lia|]. split; [rewrite ?FB_eq; clear - HFFb HF1 HF2 CE; lia|]. split; [|apply Forall_nil].
intros o Ho. rewrite ?FB_eq in Ho. apply (AF0x.apresent_writable H); [unfold TFIB_IMG_END; clear - Ho HFF HFFb HF1 HF2 Hposr; lia|].
apply (apresent_same H mem2); [apply MEQ1; rewrite unsigned_lit_small by (clear - Ho HFFb HF1 HF2 CE; lia);
[clear - Ho HFF HFFb HF1 Hposr; lia | clear - Ho HFF HFLG HFFb Hposr; lia]|].
apply PRF2. clear - Ho HFFb HFF HF1 Hposr; unfold kFakeStackSize in *; lia.
+ apply pairwise_disjoint_of_extents. unfold memC2, rFF.
let l' := eval vm_compute in (ss_mem eC1) in change (ss_mem eC1) with l'.
unfold extent_of_region. cbn [map fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite VFF, V18, V13.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
rewrite ?FB_eq, ?HOFF_eq. clear - HFF HFLG HFFb Hposr HF1 HF2. repeat split; lia. }
eapply SRr_bind; [apply (sm8_phase_to W EC PC_MEM_TO_SHADOW ssC2 _ _ _ _ HSC2 r_C2)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HFm2 & HFrm2). rewrite ?wvb_wvb in *. rewrite stC2_match in HS2.
assert (MEQ2 : forall z : word, ~ (FF <= bv_unsigned z < FF + 16384) -> ~ (F + 64 <= bv_unsigned z < F + 64 + 8) -> bv_unsigned z <> FLG ->
ms_mem ms2 z = ms_mem ms1 z).
{ intros z Hz1 Hz2 Hz3. apply HFm2. intros Hin. destruct (memC2_windows EC _ Hin) as [Hw|[Hw|Hw]];
[rewrite VFF in Hw; rewrite ?FB_eq in Hw; lia | rewrite V18 in Hw; rewrite ?HOFF_eq in Hw; lia | rewrite V13 in Hw; lia]. }
clear HFm2 HFrm2.
assert (MEQ : forall z : word, ~ (FF <= bv_unsigned z < FF + 16384) -> ~ (F + 64 <= bv_unsigned z < F + 64 + 8) -> bv_unsigned z <> FLG ->
ms_mem ms2 z = mem2 z).
{ intros z Hz1 Hz2 Hz3. rewrite (MEQ2 z Hz1 Hz2 Hz3). exact (MEQ1 z Hz2 Hz3). }
assert (MEQa : forall a, 0 <= a < 2 ^ 64 -> ~ (FF <= a < FF + 16384) -> ~ (F + 64 <= a < F + 64 + 8) -> a <> FLG ->
ms_mem ms2 (Z_to_bv 64 a) = mem2 (Z_to_bv 64 a)).
{ intros a Ha H1 H2 H3. apply MEQ; rewrite unsigned_lit_small by exact Ha; assumption. }
assert (MEQm : forall a, 0 <= a < 2 ^ 64 -> ~ (FF <= a < FF + 16384) -> ~ (F + 64 <= a < F + 64 + 8) -> a <> FLG ->
~ (sp0 - SM8_WIN <= a < sp0) -> ms_mem ms2 (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
{ intros a Ha H1 H2 H3 H4. rewrite (MEQa a Ha H1 H2 H3). exact (RAW2 a Ha H4). }
pose proof C2_facts as (PC2 & RV2 & AT2 & R1C2 & R10C2).
pose proof HS2 as HS2r.
pose proof (st_ok_restrict_mkst tfibsegs H EC _ _ HS2 RV2) as Hshape2. rewrite PC2 in Hshape2. rewrite Hshape2. rewrite Hshape2 in HS2. clear Hshape2.
assert (RD2 : forall (r : bv 5) v, reg_is eC2 (bv_unsigned r) v = true -> getr (ms_regs ms2) r = sv_denot EC v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr.
apply (st_ok_reg_denot H EC eC2 (mkst (ms_regs ms2) (Z_to_bv 64 PC_MEM_TO_SHADOW) (ms_mem ms2) (seg_rom tfibsegs)) r HS2). }
assert (G1 : getr (ms_regs ms2) 1 = Z_to_bv 64 PC_SM8_MTSRET) by (rewrite (RD2 1%bv (SLit PC_SM8_MTSRET) R1C2); reflexivity).
assert (G10 : getr (ms_regs ms2) 10 = Z_to_bv 64 FF) by (rewrite (RD2 10%bv (SOff aFF 0) R10C2); apply (DC0 _ FF VFF); clear - HFFb HF1 HF2 CE; unfold kFakeStackSize in *; lia).
rewrite restrict_mkst_fx in HS2.
(* the three regions of the phase, and what they hold *)
pose proof (st_ok_mem_ok tfibsegs EC eC2 _ HS2) as (_ & ROK2 & _). change (ms_mem (restrict H ms2)) with (mrestrict H (ms_mem ms2)) in ROK2.
destruct eC2_regions as (NR0 & NR1 & NR2).
pose proof (proj1 (Forall_forall _ _) ROK2 _ (nth_error_In _ _ NR0)) as OKFF.
pose proof (proj1 (Forall_forall _ _) ROK2 _ (nth_error_In _ _ NR1)) as OKF.
pose proof (proj1 (Forall_forall _ _) ROK2 _ (nth_error_In _ _ NR2)) as OKFLG.
unfold region_ok in OKFF, OKF, OKFLG.
destruct rFF2_shape as (BFF & WFF1 & WFF2 & CFF). destruct rF2_shape as (BF & WF1' & WF2' & CF). destruct rFLG2_shape as (BFL & WFL1 & WFL2 & CFL).
rewrite BFF in OKFF. rewrite BF in OKF. rewrite BFL in OKFLG. cbn [base_val] in OKFF, OKF, OKFLG.
rewrite VFF in OKFF. rewrite V18 in OKF. rewrite V13 in OKFLG.
destruct OKFF as (_ & _ & _ & CHFF). destruct OKF as (_ & _ & _ & CHF). destruct OKFLG as (_ & _ & _ & CHFL).
assert (DH : sv_denot EC (SOff 12%nat 1) = Z_to_bv 64 (hint' mod 2 ^ 64)).
{ cbn [sv_denot]. rewrite V12. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Zplus_mod_idemp_l, Z.mod_mod by lia. f_equal. lia. }
assert (VMH : val_mem tfibsegs (mrestrict H (ms_mem ms2)) (F + 64) 8 (hint' mod 2 ^ 64)).
{ apply (val_of_chunk_ok tfibsegs EC _ F 64 8%N (SOff 12%nat 1) _ (proj1 (Forall_forall _ _) CHF _ (nth_error_In _ _ CF)) DH); [apply Z.mod_pos_bound; cbn; lia | cbn; lia]. }
assert (VMFL : val_mem tfibsegs (mrestrict H (ms_mem ms2)) (FLG + 0) 1 1).
{ apply (val_of_chunk_ok tfibsegs EC _ FLG 0 1%N (SLit 1) 1 (proj1 (Forall_forall _ _) CHFL _ (nth_error_In _ _ CFL)) eq_refl); cbn; lia. }
assert (VMTR : val_mem tfibsegs (mrestrict H (ms_mem ms2)) (FF + 16376) 8 FLG).
{ apply (val_of_chunk_ok tfibsegs EC _ FF 16376 8%N (SOff 13%nat 0) FLG (proj1 (Forall_forall _ _) CHFF _ (nth_error_In _ _ CFF)));
[apply (DC0 _ FLG V13); clear - HFLG HF1 HF2 Hposr; unfold kFakeStackSize in *; lia | cbn; clear - HFLG HF1 HF2 Hposr CE; unfold kFakeStackSize in *; lia | cbn; lia]. }
assert (PW : forall b, (FF <= b < FF + 16384 \/ FLG <= b < FLG + 1 \/ F + 64 <= b < F + 64 + 8) -> apresent H (ms_mem ms2) b).
{ intros b Hb. destruct Hb as [Hb|[Hb|Hb]].
- apply (st_ok_window_apresent H EC eC2 ms2 0 rFF2 b HS2r NR0); [rewrite BFF, WFF1, WFF2; cbn [base_val]; rewrite VFF; rewrite ?FB_eq; lia | unfold TFIB_IMG_END; clear - Hb HFF HFFb HF1 HF2 Hposr CE; lia].
- apply (st_ok_window_apresent H EC eC2 ms2 2 rFLG2 b HS2r NR2); [rewrite BFL, WFL1, WFL2; cbn [base_val]; rewrite V13; lia | unfold TFIB_IMG_END; clear - Hb HFLG HF1 HF2 Hposr CE; unfold kFakeStackSize in *; lia].
- apply (st_ok_window_apresent H EC eC2 ms2 1 rF2 b HS2r NR1); [rewrite BF, WF1', WF2'; cbn [base_val]; rewrite V18; rewrite ?HOFF_eq; lia | unfold TFIB_IMG_END; clear - Hb HF1 HF2 CE; lia]. }
assert (AVQ : forall a, 0 <= a < 2 ^ 64 -> ~ (FF <= a < FF + 16384 \/ FLG <= a < FLG + 1 \/ F + 64 <= a < F + 64 + 8) ->
aview tfibsegs H (ms_mem ms2) a = aview tfibsegs H mem2 a).
{ intros a Ha Hn. apply aview_same. apply MEQ; rewrite unsigned_lit_small by exact Ha; clear - Hn; lia. }
(* ---- AR for the post state, at the MemToShadow call ---- *)
assert (HAR' : AR tfibsegs B ly S' W (ms_mem ms2) (with_vm_backing (m_vm_lazy md2) mat2 md2)).
{ rewrite HS'eq. apply (astack_malloc_law_ok tfibsegs B ly S W mem2 md2 (ms_mem ms2) _ CID8 pos hint' HAR2 ltac:(unfold CID8; lia) Hprobe2).
all: change (w_H W) with H.
- intros k Hk. replace (ly_F ly + 8 * CID8 + Z.of_nat k) with (F + 64 + Z.of_nat k) by (unfold CID8; subst F; lia).
rewrite (aview_of_val_mem H (ms_mem ms2) _ 8 _ k VMH Hk). unfold YG0f.le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
- fold FLG. pose proof (aview_of_val_mem H (ms_mem ms2) _ 1 _ 0 VMFL ltac:(lia)) as X. rewrite !Z.add_0_r in X. exact X.
- intros a Ha Hown Nh Nf Nfr Nsh. apply AVQ; [exact Ha|]. intros [Hs|[Hs|Hs]].
+ apply Nfr. unfold in_zr. cbn [fst snd]. try fold FF. change (fs_frame_bytes CID8) with 16384. lia.
+ apply Nf. try fold FLG. lia.
+ apply Nh. replace (ly_F ly) with F by reflexivity. unfold CID8. lia.
- intros a Hv. rewrite (AE2y.aview_mod _ (ms_mem ms2) a). rewrite (AE2y.aview_mod _ mem2 a) in Hv.
pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Hr. set (a' := a mod 2 ^ 64) in *. clearbody a'.
assert (CS : (FF <= a' < FF + 16384 \/ FLG <= a' < FLG + 1 \/ F + 64 <= a' < F + 64 + 8) \/
~ (FF <= a' < FF + 16384 \/ FLG <= a' < FLG + 1 \/ F + 64 <= a' < F + 64 + 8)) by (clear; lia).
destruct CS as [CS|CS]; [apply AE2y.aview_some_of_apresent; apply PW; exact CS | rewrite (AVQ a' Hr CS); exact Hv].
- reflexivity. - reflexivity. - reflexivity.
- refine (hs_kept_gen H mem2 (ms_mem ms2) (fun b => FF <= b < FF + 16384 \/ FLG <= b < FLG + 1 \/ F + 64 <= b < F + 64 + 8) _ _).
+ intros z Hz. apply MEQ; clear - Hz; lia.
+ intros b Hb. exists (ms_mem ms2). exact (PW b Hb). }
(* ---- the MemToShadow call: the one place the published summary is used ---- *)
assert (HRET : YK0s.ret_ok (getr (ms_regs ms2) 1)).
{ unfold YK0s.ret_ok. rewrite G1. vm_compute. reflexivity. }
assert (G10w : getr (ms_regs ms2) 10 = w64 FF) by (unfold w64; exact G10).
eapply SRr_bind;
[exact (MTS ly S' W (ms_regs ms2) (ms_mem ms2) (with_vm_backing (m_vm_lazy md2) mat2 md2) CID8 pos FF
HAR' HRET ltac:(unfold CID8; lia) ltac:(rewrite fs_frames_cid8; clear - Hposr; lia) G10w
ltac:(try fold FF; lia) ltac:(try fold FF; change (fs_frame_bytes CID8) with 16384; lia))|].
cbv beta. intros W3 c3 _ (-> & regsM & memM & mdM & Hc3 & HARM & HREGM & HMDM & G10M & MVIEW & MPRES).
assert (RAZ : raZ (ms_regs ms2) = PC_SM8_MTSRET) by (unfold raZ; rewrite G1; apply unsigned_lit_small; unfold PC_SM8_MTSRET, PC_SM8_FOUND; lia).
rewrite RAZ in Hc3. subst c3.
(* ---- phase 3: the four moves after the call, into PoisonShadow ---- *)
set (E3 := Ereg regsM (@nil word)) in *.
assert (E3reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E3 i = getr regsM r) by (intros; subst E3; apply ew_Ereg_nat; assumption).
assert (HSC3 : st_ok tfibsegs E3 ssC3 (restrict H (mkst regsM (Z_to_bv 64 PC_SM8_MTSRET) memM (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssC3. apply (entry_st_ok_full tfibsegs); change (Ereg regsM (@nil word)) with E3.
- apply regs_ok_Ereg.
- reflexivity.
- apply Forall_nil.
- exact I.
- split; [exact I|]. split; exact I. }
unfold cfg_at.
eapply SRr_bind; [apply (sm8_phase_to W E3 PC_POISON_SHADOW ssC3 _ _ _ _ HSC3 r_C3)|].
cbv beta. intros W4 c4 _ (-> & ms3 & mat3 & -> & HS3 & HFm3 & HFrm3). rewrite ?wvb_wvb in *. rewrite stC3_match in HS3.
pose proof C3_facts as (PC3 & RV3 & MEM3 & R1C3 & R10C3 & R11C3 & R12C3 & FBC3).
assert (MEQ3 : forall z : word, ms_mem ms3 z = memM z).
{ intros z. apply HFm3. intros (r & Hr & _). vm_compute in Hr. exact Hr. }
clear HFm3 HFrm3.
pose proof (st_ok_restrict_mkst tfibsegs H E3 _ _ HS3 RV3) as Hshape3. rewrite PC3 in Hshape3. rewrite Hshape3.
assert (RD3 : forall (r : bv 5) v, reg_is eC3 (bv_unsigned r) v = true -> getr (ms_regs ms3) r = sv_denot E3 v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr.
apply (st_ok_reg_denot H E3 eC3 ms3 r). exact HS3. }
assert (KEEPM : forall r : bv 5, In (bv_unsigned r) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
getr regsM r = getr (ms_regs ms2) r).
{ intros r Hin. rewrite <- (Z_to_bv_bv_unsigned 5 r). apply HREGM. unfold acallee_saved. clear - Hin. cbn in Hin. lia. }
assert (KEEP3 : forall r : bv 5, In (bv_unsigned r) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
getr (ms_regs ms3) r = getr regsM r).
{ intros r Hin. rewrite forallb_forall in FBC3. pose proof (FBC3 _ Hin) as Hrz. cbn beta in Hrz.
pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
rewrite (RD3 r (SOff (Z.to_nat (bv_unsigned r)) 0) Hrz).
cbn [sv_denot]. rewrite (E3reg (Z.to_nat (bv_unsigned r)) r) by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (KEEP : forall r : bv 5, In (bv_unsigned r) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
getr (ms_regs ms3) r = getr (ms_regs ms2) r).
{ intros r Hin. rewrite (KEEP3 r Hin). exact (KEEPM r Hin). }
(* the registers Seg C hands to Seg D *)
assert (Q18 : getr (ms_regs ms2) 18 = Z_to_bv 64 FF).
{ rewrite (RD2 18%bv (SOff aFF 0) ltac:(vm_compute; reflexivity)).
apply (DC0 _ FF VFF); clear - HFFb HF1 HF2 CE; unfold kFakeStackSize in *; lia. }
assert (Q9 : getr (ms_regs ms2) 9 = Z_to_bv 64 n).
{ rewrite (RD2 9%bv (SOff 9%nat 0) ltac:(vm_compute; reflexivity)).
cbn [sv_denot]. rewrite (ECreg 9%nat 9%bv eq_refl), R9, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (Q2 : getr (ms_regs ms2) 2 = Z_to_bv 64 (sp0 - SM8_FRAME)).
{ rewrite (RD2 2%bv (SOff 2%nat 0) ltac:(vm_compute; reflexivity)).
cbn [sv_denot]. rewrite (ECreg 2%nat 2%bv eq_refl), R2, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (Q8 : getr (ms_regs ms2) 8 = Z_to_bv 64 sp0).
{ rewrite (RD2 8%bv (SOff 8%nat 0) ltac:(vm_compute; reflexivity)).
cbn [sv_denot]. rewrite (ECreg 8%nat 8%bv eq_refl), R8, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (G1F : getr (ms_regs ms3) 1 = Z_to_bv 64 PC_SM8_MSRET) by (rewrite (RD3 1%bv (SLit PC_SM8_MSRET) R1C3); reflexivity).
assert (G10F : getr (ms_regs ms3) 10 = Z_to_bv 64 FF).
{ rewrite (RD3 10%bv (SOff 18%nat 0) R10C3). cbn [sv_denot]. rewrite (E3reg 18%nat 18%bv eq_refl), Z.add_0_r.
rewrite (KEEPM 18%bv ltac:(vm_compute; lia)), Q18, Z_to_bv_bv_unsigned. reflexivity. }
assert (G11F : getr (ms_regs ms3) 11 = Z_to_bv 64 n).
{ rewrite (RD3 11%bv (SOff 9%nat 0) R11C3). cbn [sv_denot]. rewrite (E3reg 9%nat 9%bv eq_refl), Z.add_0_r.
rewrite (KEEPM 9%bv ltac:(vm_compute; lia)), Q9, Z_to_bv_bv_unsigned. reflexivity. }
assert (G12F : getr (ms_regs ms3) 12 = Z_to_bv 64 0) by (rewrite (RD3 12%bv (SLit 0) R12C3); reflexivity).
(* ---- the post ---- *)
apply SRr_ret. split; [reflexivity|].
exists (ms_regs ms3), (ms_mem ms3), (with_vm_backing (m_vm_lazy mdM) mat3 mdM).
split; [reflexivity|].
assert (AVM : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs H (ms_mem ms3) a = aview tfibsegs H (ms_mem ms2) a).
{ intros a Ha. rewrite (aview_same H memM (ms_mem ms3) a (MEQ3 _)). exact (MVIEW a Ha). }
assert (PRM : forall a, apresent H (ms_mem ms2) a -> apresent H (ms_mem ms3) a).
{ intros a Hp. apply (apresent_same H memM); [exact (MEQ3 _) | exact (MPRES a Hp)]. }
split.
- (* AR S' *)
pose proof (same_but_materialized_frame mdM _ (with_vm_backing_same mdM mat3)) as MF3.
apply (al_frame _ _ LAWS ly S' W memM mdM (ms_mem ms3) (with_vm_backing (m_vm_lazy mdM) mat3 mdM) HARM).
all: change (w_H W) with H.
+ intros a Ha _. apply aview_same. exact (MEQ3 _).
+ intros a Hv. rewrite (aview_same H memM (ms_mem ms3) a (MEQ3 _)). exact Hv.
+ apply MF3. + apply MF3. + apply MF3.
+ intros a Ha Hh. exact (MEQ3 _).
- split; [exact G1F|]. split; [exact G10F|]. split; [exact G11F|]. split; [exact G12F|].
split; [rewrite (KEEP 2%bv ltac:(vm_compute; lia)); exact Q2|].
split; [rewrite (KEEP 8%bv ltac:(vm_compute; lia)); exact Q8|].
split; [rewrite (KEEP 9%bv ltac:(vm_compute; lia)); exact Q9|].
split; [rewrite (KEEP 18%bv ltac:(vm_compute; lia)); exact Q18|].
split; [rewrite fs_frames_cid8; clear - Hposr; lia|].
split.
{ (* sm8_regs_kept *)
intros r Hr.
assert (Hr32 : 0 <= r < 32) by (clear - Hr; lia).
assert (U5 : bv_unsigned (Z_to_bv 5 r) = r) by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 5) with 32; apply Z.mod_small; exact Hr32).
rewrite (KEEP (Z_to_bv 5 r) ltac:(rewrite U5; clear - Hr; cbn; lia)).
assert (HKC : reg_is eC2 r (SOff (Z.to_nat r) 0) = true).
{ clear - Hr. destruct Hr as [->|[->|Hr]]; [vm_compute; reflexivity | vm_compute; reflexivity|].
assert (E : r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
decompose [or] E; subst; vm_compute; reflexivity. }
rewrite (RD2 (Z_to_bv 5 r) (SOff (Z.to_nat r) 0)); [|rewrite U5; exact HKC].
cbn [sv_denot]. rewrite (ECreg (Z.to_nat r) (Z_to_bv 5 r)) by (rewrite U5; lia). rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
apply Hkept2. exact Hr. }
split.
{ (* sm8_saved *) pose proof Hsaved2 as (S1 & S2 & S3 & S4 & S5).
assert (AVS : forall a, sp0 - 40 <= a < sp0 -> aview tfibsegs H (ms_mem ms3) a = aview tfibsegs H mem2 a).
{ intros a Ha. rewrite (AVM a ltac:(clear - Ha Hsp44; lia)). apply AVQ; [clear - Ha Hsp44; lia|].
clear - Ha Hsp44 HFF HFLG HFFb HF1 HF2 DFS Hslo Htop Hposr. unfold kFakeStackSize in *. lia. }
assert (RW : forall a v, sp0 - 40 <= a -> a + 8 <= sp0 -> rdword (aview tfibsegs H mem2) a = Some v -> rdword (aview tfibsegs H (ms_mem ms3)) a = Some v).
{ intros a v Ha1 Ha2 Hv. rewrite <- Hv. apply rdword_ext. intros i Hi. apply AVS. lia. }
split; [apply RW; [lia | lia | exact S1]|]. split; [apply RW; [lia | lia | exact S2]|].
split; [apply RW; [lia | lia | exact S3]|]. split; [apply RW; [lia | lia | exact S4] | apply RW; [lia | lia | exact S5]]. }
split.
{ (* sm8_stack_pres *) intros a Ha. apply PRM. apply (apresent_same H mem2).
- apply MEQa; clear - Ha Hsp44 HFF HFLG HFFb HF1 HF2 DFS Hslo Htop Hposr;
unfold ESTACK, kFakeStackSize in *; lia.
- apply Hpres2. exact Ha. }
split.
{ (* same_but_materialized *) eapply same_but_materialized_trans; [exact Hmd2|].
eapply same_but_materialized_trans; [apply with_vm_backing_same|].
eapply same_but_materialized_trans; [exact HMDM | apply with_vm_backing_same]. }
split.
{ (* the memory outside the walk's windows *) intros a Ha Hstk Hhint Hflag Hframe.
rewrite (AVM a Ha). rewrite (AVQ a Ha); [|intros [Hs|[Hs|Hs]];
[apply Hframe; try fold FF; change (fs_frame_bytes CID8) with 16384; lia
| apply Hflag; try fold FLG; lia
| apply Hhint; replace (ly_F ly) with F by reflexivity; unfold CID8 in Hs |- *; lia]].
apply aview_same. apply RAW2; [exact Ha | exact Hstk]. }
split.
{ (* the back pointer at the top of the frame *) try fold FF. try fold FLG. change (fs_frame_bytes CID8) with 16384.
rewrite (rdword_ext (aview tfibsegs H (ms_mem ms2)) (aview tfibsegs H (ms_mem ms3)) (FF + 16384 - 8)
ltac:(intros i Hi; apply AVM; clear - Hi HFFb HF1 HF2 CE; lia)).
replace (FF + 16384 - 8) with (FF + 16376) by lia.
apply (AF0x.val_mem_rdword H (ms_mem ms2) _ FLG); [clear - HFLG HF1 HF2 Hposr CE; unfold kFakeStackSize in *; lia | exact VMTR]. }
split.
{ (* the frame is present *) intros a Ha. apply PRM. apply PW. left. try fold FF in Ha. change (fs_frame_bytes CID8) with 16384 in Ha. lia. }
{ (* the frame's shadow is present *) intros a Ha.
try fold FF in Ha. change (fs_frame_bytes CID8 / 8) with 2048 in Ha. rewrite HSH in Ha.
assert (HA64 : 0 <= a < 2 ^ 64) by (clear - Ha HF1 HF2 HF8 CE Hposr; lia).
apply PRM. apply (apresent_same H mem2).
- apply MEQa; clear - Ha HA64 HFF HFLG HFFb HSHF HSH HF1 HF2 HF8 CE Hposr;
unfold kFakeStackSize in *; lia.
- apply (apresent_same H mem).
+ apply RAW2; [exact HA64 | clear - Ha HSHF HSH HF1 HF2 HF8 CE Hposr Hslo Htop Lbeg DFS; unfold SM8_WIN, kFakeStackSize in *; lia].
+ apply PRS. unfold shadow_addr, SHADOW_OFF, kFakeFramesOff.
replace ((F + (4096 + 32768)) / 8) with (F / 8 + 4608) by (replace (F + (4096 + 32768)) with ((F / 8 + 4608) * 8) by (clear - HF8; lia); rewrite Z_div_mult by lia; reflexivity).
clear - Ha Hposr. lia. }
Qed.
End f.
End d.
