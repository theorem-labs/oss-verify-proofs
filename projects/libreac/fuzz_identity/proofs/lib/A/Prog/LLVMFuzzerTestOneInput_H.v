(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Segment H of LLVMFuzzerTestOneInput's ASan walk: the "any firmware value" block, 0x817bc..0x81878.
   seg_H of lib/A/Prog/LLVMFuzzerTestOneInput_inv.v, from inv_G_end to inv_H_end.

   The code (BASE + 0x10b0 .. BASE + 0x116c), fw = SlotModel.t_any_fw (x21), v1 = fw / 1000 (x18):
     0x817bc jal put_dec            put_dec(ef, mf+208, v1, 1): DEC v1 1 at ef, mf+208 := n1 (tput_dec_spec)
     0x817c0 .. 0x817e8              the shadow test of ef[n1] (0x817d4 lb, 0x817e0 bnez), mf+208 := n1 + 1,
                                    ef[n1] := '.'
     0x817ec .. 0x8180c              a2 = fw mod 1000; put_dec(ef, mf+208, fw mod 1000, 3): DEC _ 3 at ef+n1+1
     0x81810 .. 0x81840              s6 = n2 = n1 + 4; the shadow test of ef[n2]; s11 = mf+144; ef[n2] := 0
     0x81844 jal reac_identity_fw_str  fw_str(fw, f, 8): FW fw and a NUL at f, a0 = L fw (treac_identity_fw_str_spec)
     0x81848 bltz a0 / 0x8184c bne s6,a0   both decided: L fw = n2 (reac_identity_fw_str_c3_len)
     0x8185c jal bcmp               bcmp(f, ef, n2 + 1) (YCbq.aj_bcmp_at): FW fw = t_EF (reac_identity_fw_str_c3)
     0x81860 bnez a0                decided by the bcmp result
     0x81864 .. 0x81874              a1 = s7 << 56; the shadow of f and ef poisoned again (0xf8 at s3+58, +62, +63)
   Every run is a plain run (no checked access through the token engine): the two shadow tests read the cell of
   ef through an alias of the symbolic state, the poisoning writes the frame's shadow window. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv put_dec reac_identity_fw_str.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec put_dec_c
  reac_identity_fw_str_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b turns lia's division and modulo handling off for every file that loads it; the shadow arithmetic of this
   segment needs it, so this file turns it back on. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic states ------------------------------------------------------------------------------------ *)
(* Atoms 0..31: the registers at the start of the run; 32: SHADOW_OFF; 33: the shadow cell of ef (SF+496);
   34: t_cap_disp (mf+144); 35: the counter n at mf+208; 36: ef + n, the byte the run stores. *)
Definition h_SB : Z := 0x7fff8000.
(* the machine-frame words the runs read: mf+80 = SF (= ef - 496), mf+144 = t_cap_disp, mf+176 = SHADOW_OFF *)
Definition h_mf : YP09.region := YP09.mkRegion (Some 9%nat) 80 184 80 80
  [YP09.mkChunk 80 (CVal 8 (SOff 20 (-496))); YP09.mkChunk 144 (CVal 8 (SOff 34 0));
   YP09.mkChunk 176 (CVal 8 (SOff 32 0))].
(* the counter slot mf+208 (put_dec's `n`), written by the run *)
Definition h_n : YP09.region := YP09.mkRegion (Some 9%nat) 208 216 208 216 [YP09.mkChunk 208 (CVal 8 (SOff 35 0))].
(* ef's first shadow cell, read by the two shadow tests *)
Definition h_sh : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
(* the byte ef + n the run writes ('.' in run 1, the NUL in run 2) *)
Definition h_dot : YP09.region := YP09.mkRegion (Some 36%nat) 0 1 0 1 [].
(* ef + n is atom 36; its shadow cell is atom 33 (bx: the register that holds SHADOW_OFF, s9 after its load) *)
Definition h_facts (bx : nat) : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (20%nat, mkAF 4096 (2 ^ 47) 4);
           (32%nat, mkAF h_SB h_SB 0); (33%nat, mkAF h_SB (h_SB + 2 ^ 44) 0); (35%nat, mkAF 1 6 0);
           (36%nat, mkAF 4096 (2 ^ 47) 0)] []
          [(SAlu ALU_ADD (SOff 20 0) (SOff 35 0), SOff 36 0);
           (SAlu ALU_ADD (SAlu ALU_SRL (SOff 36 0) (SLit 3)) (SOff bx 0), SOff 33 0)].
Definition ss_h0 : sstate := mkSS 0x10b0 sr_atoms [] None (mkFacts [] [] []).
Definition ss_h1 : sstate := mkSS 0x10b4 sr_atoms [h_mf; h_n; h_sh; h_dot] None (h_facts 32).
Definition ss_h2 : sstate := mkSS 0x1104 sr_atoms [h_mf; h_n; h_sh; h_dot] None (h_facts 25).
Definition ss_h3 : sstate := mkSS 0x113c sr_atoms [] None (mkFacts [] [] []).
(* the frame's shadow, base s3 (atom 19), writable on the cells of f and ef *)
Definition h_s3 : YP09.region := YP09.mkRegion (Some 19%nat) 0 128 58 64 [].
Definition ss_h4 : sstate := mkSS 0x1154 sr_atoms [h_s3] None (mkFacts [] [] []).

(* 0x817ec..0x817fc: a2 = (fw - (fw / 1000) * 1000) mod 2^16 = fw mod 1000, checked for every fw < 2^16 *)
Definition h_M1000 : sv :=
  SAlu ALU_SRL (SAlu ALU_SLL (SAluw ALU_SUB (SOff 21 0) (SMd M_MUL (SOff 18 0) (SLit 1000))) (SLit 48)) (SLit 48).
Definition h_Efw (x : Z) : env := mkEnv (fun n => if Nat.eqb n 21 then Z_to_bv 64 x else Z_to_bv 64 (x / 1000)) (fun _ => []).
Lemma h_m1000_check :
  fw_zall (fun x => bv_eqb (sv_denot (h_Efw x) h_M1000) (Z_to_bv 64 (x mod 1000))) (Z.to_nat 65536) 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma h_m1000 : forall E x, ew E 21 = Z_to_bv 64 x -> ew E 18 = Z_to_bv 64 (x / 1000) -> 0 <= x < 65536 ->
  sv_denot E h_M1000 = Z_to_bv 64 (x mod 1000).
Proof.
intros E x H21 H18 Hx.
assert (Hag : sv_denot E h_M1000 = sv_denot (h_Efw x) h_M1000)
  by (unfold h_M1000; cbn [sv_denot h_Efw ew Nat.eqb]; rewrite H21, H18; reflexivity).
rewrite Hag. pose proof (fw_zall_spec _ _ _ h_m1000_check x ltac:(lia)) as H.
unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq in H. exact H.
Qed.
(* 0x81868: a1 = t_fam_raw << 56, checked for every byte value *)
Definition h_SLL56 : sv := SAlu ALU_SLL (SOff 23 0) (SLit 56).
Definition h_Efam (x : Z) : env := mkEnv (fun _ => Z_to_bv 64 x) (fun _ => []).
Lemma h_sll_check :
  fw_zall (fun x => bv_eqb (sv_denot (h_Efam x) h_SLL56) (Z_to_bv 64 (x * 2 ^ 56))) (Z.to_nat 256) 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma h_sll56 : forall E x, ew E 23 = Z_to_bv 64 x -> 0 <= x < 256 ->
  sv_denot E h_SLL56 = Z_to_bv 64 (x * 2 ^ 56).
Proof.
intros E x H23 Hx.
assert (Hag : sv_denot E h_SLL56 = sv_denot (h_Efam x) h_SLL56)
  by (unfold h_SLL56; cbn [sv_denot h_Efam ew]; rewrite H23; reflexivity).
rewrite Hag. pose proof (fw_zall_spec _ _ _ h_sll_check x ltac:(lia)) as H.
unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq in H. exact H.
Qed.
Ltac prreg_raw HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section of LLVMFuzzerTestOneInput.v / _inv.v, in the same order. *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
(* What this segment needs, each as the contract's Section states it (LLVMFuzzerTestOneInput.v, _inv.v). *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis HEV : EV_LLVMF <= EV_LIB.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PSIG : ident_prog_sig_ok (PI := PI).
Hypothesis MTL : ameter_laws MT.
Hypothesis HMT0 : forall s s' : astate, mo_le MT s s' 0.
Hypothesis HPD : tput_dec_spec B.
Hypothesis HFWS : treac_identity_fw_str_spec B.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA IS___interceptor_trampoline_bcmp).
(* cgif ACfh.v:162-164 *)
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (PI := PI).

(* ---- the callees' premises for the two kinds of buffer the segment passes ------------------------------------- *)
Lemma h_mod4096_mod8 : forall x, x mod 4096 = 0 -> x mod 8 = 0.
Proof. intros x H. apply Z.mod_divide in H; [|lia]. apply Z.mod_divide; [lia|]. destruct H as [q ->]. exists (512 * q). lia. Qed.
(* bytes of the machine stack above sp, inside the caller's window: their shadow is the stack's zero shadow *)
Lemma h_tsrc_stack : forall STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k sp q n,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
  sp0 - STK <= q -> q + n + 64 <= sp0 -> 0 < n -> sp <= q ->
  tsrc_ok W memc sp q n.
Proof.
intros STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k sp q n HJ Hlo Hhi Hn Hsp.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & Hpal & Hpah & _).
unfold page_aligned in Hpal, Hpah.
pose proof (al_zshadow _ _ LAWS lyc Sc W memc mdc (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc)
  HAR ltac:(left; reflexivity)) as Hz. cbn [fst snd] in Hz.
rewrite Elo, Ehi in Hz. rewrite Elo in Hpal. rewrite Ehi in Hpah.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (lo := ly_stk_lo ly) in *. set (hi := ly_stk_hi ly) in *.
assert (Dlo : lo = 4096 * (lo / 4096)) by (clear - Hpal; lia).
assert (Dhi : hi = 4096 * (hi / 4096)) by (clear - Hpah; lia).
split.
{ intros a Ha. split; [apply (aview_some_of_apresent SEGS); apply Hpres; lia | lia]. }
split.
{ eapply range_addressable_sub; [apply zero_shadow_range; [exact (h_mod4096_mod8 _ Hpal) | | exact Hz] | lia | lia].
  clear - Dlo Dhi. lia. }
split.
{ intros s Hs. unfold shadow_addr, SHADOW_OFF in Hs.
  assert (Hi : 0 <= s - shadow_of_addr SHADOW_OFF lo < (hi - lo) / 8).
  { unfold shadow_of_addr, SHADOW_OFF. clear - Hs Dlo Dhi Hlo Hhi Hslo Hshi Hn. lia. }
  specialize (Hz _ Hi). replace (shadow_of_addr SHADOW_OFF lo + (s - shadow_of_addr SHADOW_OFF lo)) with s in Hz by lia.
  rewrite Hz. discriminate. }
split; [unfold amem_range; right; rewrite C3, C4; lia|].
lia.
Qed.
(* bytes of a side-stack frame inside an 8-aligned range whose shadow is zero *)
Lemma h_tsrc_frame : forall STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k sp cid pos a0 N q n,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k -> In (cid, pos) (frames Sc) ->
  frame_addr lyc cid pos <= a0 -> a0 + N <= frame_addr lyc cid pos + fs_frame_bytes cid ->
  a0 mod 8 = 0 -> N mod 8 = 0 -> zero_shadow (aview SEGS (w_H W) memc) SHADOW_OFF a0 N ->
  a0 <= q -> q + n <= a0 + N -> 0 < n -> alloc_ceiling <= sp - ESTACK ->
  tsrc_ok W memc sp q n.
Proof.
intros STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k sp cid pos a0 N q n HJ Hin H1 H2 Ha0 HN Hz Hq1 Hq2 Hn Hsp.
pose proof HJ as (HAR & _).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc cid pos HAR Hin) as (_ & Happ & Hpres & _).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F0 & F1 & _).
pose proof asan_consts as (C1 & _).
split.
{ intros a Ha. split; [apply (aview_some_of_apresent SEGS); apply Hpres; lia | lia]. }
split; [eapply range_addressable_sub; [apply zero_shadow_range; [exact Ha0 | exact HN | exact Hz] | lia | lia]|].
split; [apply (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc W memc mdc cid pos); [exact HAR | exact Hin | lia | lia | lia]|].
split; [apply (amem_range_sub_app (frame_addr lyc cid pos) (fs_frame_bytes cid)); [exact Happ | lia | lia | lia | lia]|].
lia.
Qed.
(* moving facts about bytes from one memory to another that agrees on them *)
Lemma h_vm1 : forall H mem a v, aview SEGS H mem a = Some v -> val_mem SEGS (mrestrict H mem) a 1 v.
Proof.
intros H mem a v Hv j Hj. assert (j = 0%nat) by lia. subst j. rewrite Z.add_0_r.
destruct (aview_byte SEGS H mem a v Hv) as (b & Hb & -> & Hr). rewrite Hb. f_equal.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, YO0f.le_byte. change (bv_modulus 8) with 256.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
rewrite !(Z.mod_small (bv_unsigned b) 256 Hr). reflexivity.
Qed.
Lemma h_garr8_moved : forall H H' (m m' : word -> option byte) a l,
  (forall k, 0 <= k < Z.of_nat (length l) -> aview SEGS H' m' (a + k) = aview SEGS H m (a + k)) ->
  garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved SEGS H H' m m' (a + Z.of_nat j) (a + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros k Hk1. replace (a + Z.of_nat j + k) with (a + (Z.of_nat j + k)) by lia. apply Hk. lia.
Qed.
Lemma h_garr8_app : forall m a (l1 l2 : list Z),
  garr8 SEGS m a l1 -> garr8 SEGS m (a + Z.of_nat (length l1)) l2 -> garr8 SEGS m a (l1 ++ l2).
Proof.
intros m a l1 l2 H1 H2 j Hj. rewrite length_app in Hj.
destruct (Nat.lt_ge_cases j (length l1)) as [Hlt | Hge].
- rewrite app_nth1 by exact Hlt. exact (H1 j Hlt).
- rewrite app_nth2 by exact Hge.
  destruct (H2 (j - length l1)%nat ltac:(lia)) as [Hv Hr]. split; [|exact Hr].
  replace (a + Z.of_nat j) with (a + Z.of_nat (length l1) + Z.of_nat (j - length l1)) by lia. exact Hv.
Qed.
Lemma h_garr8_aview : forall H mem a (l : list Z) j,
  garr8 SEGS (mrestrict H mem) a l -> (j < length l)%nat -> aview SEGS H mem (a + Z.of_nat j) = Some (nth j l 0).
Proof. intros H mem a l j Hg Hj. destruct (Hg j Hj) as [Hv Hr]. exact (aview_of_val_mem1 SEGS H mem _ _ Hv Hr). Qed.
Lemma h_garr8_prefix : forall m a (l1 l2 : list Z), garr8 SEGS m a (l1 ++ l2) -> garr8 SEGS m a l1.
Proof.
intros m a l1 l2 Hg j Hj. destruct (Hg j ltac:(rewrite length_app; lia)) as [Hv Hr].
rewrite app_nth1 in Hv, Hr by exact Hj. exact (conj Hv Hr).
Qed.
Lemma h_zs_moved : forall (rd rd' : reader) Bs a n,
  (forall i, 0 <= i < n / 8 -> rd' (shadow_of_addr Bs a + i) = rd (shadow_of_addr Bs a + i)) ->
  zero_shadow rd Bs a n -> zero_shadow rd' Bs a n.
Proof. intros rd rd' Bs a n Hk Hz i Hi. rewrite (Hk i Hi). exact (Hz i Hi). Qed.
Lemma h_bs_moved : forall (rd rd' : reader) Bs a n,
  (forall i, 0 <= i < (n + 7) / 8 -> rd' (shadow_of_addr Bs a + i) = rd (shadow_of_addr Bs a + i)) ->
  block_shadow rd Bs a n -> block_shadow rd' Bs a n.
Proof. intros rd rd' Bs a n Hk (H0 & H1 & Hz). split; [exact H0|]. split; [exact H1|]. intros i Hi. rewrite (Hk i Hi). exact (Hz i Hi). Qed.
(* a value the symbolic state holds in a region chunk is in memory *)
Lemma h_val_of_st_ok : forall E ss ms r nb off (sz : N) e v,
  st_ok SEGS E ss ms -> In r (ss_mem ss) -> YP09.r_base r = Some nb ->
  In (YP09.mkChunk off (CVal sz e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N sz) -> Z.of_N sz <= 8 ->
  val_mem SEGS (ms_mem ms) (bv_unsigned (ew E nb) + off) (N.to_nat sz) v.
Proof.
intros E ss ms r nb off sz e v HS Hin Hb Hc He Hv Hsz.
pose proof (st_ok_mem_ok SEGS E _ ms HS) as HM.
pose proof (mem_ok_region SEGS E (ms_mem ms) _ r HM Hin) as (_ & _ & _ & Hcs).
rewrite Hb in Hcs. cbn [base_val] in Hcs.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck.
exact (val_of_chunk_ok SEGS E (ms_mem ms) _ off sz e v Hck He Hv Hsz).
Qed.
(* What a caller-journal callee kept, for the four kinds of address the boundaries speak of: the machine stack
   above the callee's window, the frame (4, pos), its shadow, and the heap blocks of the run. *)
Lemma h_keep_tcj : forall STK' lyc Sc W memc W' mem' sp (E : Z -> Prop) (Cbl : list (Z * Z)) pos SFx (WR : Z -> Prop),
  tcj_kept B STK' lyc Sc W memc W' mem' sp E ->
  frames Sc = [(4, pos)] -> frame_addr lyc 4 pos = SFx ->
  (forall b n, In (b, n) Cbl -> In (b, n) (ablocks B lyc Sc)) ->
  (forall a, sp - STK' <= a < sp -> WR a) -> (forall a, E a -> WR a) ->
  forall a, 0 <= a < 2 ^ 64 ->
  ((alloc_ceiling <= a) \/ (SFx <= a < SFx + 1024) \/ (shadow_addr SFx <= a < shadow_addr SFx + 128) \/
   (exists b n j, In (b, n) Cbl /\ 0 <= j < req_size n /\ a = b + j)) ->
  ~ WR a -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) memc a.
Proof.
intros STK' lyc Sc W memc W' mem' sp E Cbl pos SFx WR (K1 & K2 & _ & K4 & _) Hfr EFx Hbl Hwin HE a Ha Hcl Hw.
destruct Hcl as [Hc | [Hc | [Hc | (b & n & j & Hin & Hj & ->)]]].
- apply K1; [lia | intros H; apply Hw, Hwin; exact H | intros H; apply Hw, HE; exact H].
- apply (K4 4 pos a); [rewrite Hfr; left; reflexivity | | intros H; apply Hw, HE; exact H].
  left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFx. change (fs_frame_bytes 4) with 1024. lia.
- apply (K4 4 pos a); [rewrite Hfr; left; reflexivity | | intros H; apply Hw, HE; exact H].
  right. unfold in_zr. cbn [fst snd]. rewrite EFx. change (fs_frame_bytes 4 / 8) with 128. lia.
- apply (K2 b n j); [apply Hbl; exact Hin | exact Hj | intros H; apply Hw, HE; exact H].
Qed.
(* ---- the symbolic state of runs 1 and 2 -------------------------------------------------------------------- *)
Definition h_E (regs : bvmap 5 word) (sh cd n SF : Z) : env :=
  Eimg (Ereg regs (map (Z_to_bv 64) [h_SB; sh + 62; cd; n; SF + 496 + n])).
Lemma h_E_reg : forall regs sh cd n SF k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (h_E regs sh cd n SF) k = getr regs r.
Proof. intros regs sh cd n SF k r Hk. unfold h_E. apply ew_Eimg_Ereg_nat. exact Hk. Qed.
Lemma h_E_ext : forall regs sh cd n SF,
  ew (h_E regs sh cd n SF) 32 = Z_to_bv 64 h_SB /\ ew (h_E regs sh cd n SF) 33 = Z_to_bv 64 (sh + 62) /\
  ew (h_E regs sh cd n SF) 34 = Z_to_bv 64 cd /\ ew (h_E regs sh cd n SF) 35 = Z_to_bv 64 n /\
  ew (h_E regs sh cd n SF) 36 = Z_to_bv 64 (SF + 496 + n).
Proof.
intros regs sh cd n SF. unfold h_E. rewrite !Eimg_low by (unfold A_TEXT; lia).
split; [exact (ew_Ereg_extra regs _ 0)|]. split; [exact (ew_Ereg_extra regs _ 1)|].
split; [exact (ew_Ereg_extra regs _ 2)|]. split; [exact (ew_Ereg_extra regs _ 3)|]. exact (ew_Ereg_extra regs _ 4).
Qed.
Lemma h_E_agree : forall regs sh cd n SF,
  env_agree 32 (Ereg regs (map (Z_to_bv 64) [h_SB; sh + 62; cd; n; SF + 496 + n])) (h_E regs sh cd n SF).
Proof. intros. unfold h_E. split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
Lemma h_E_img : forall regs sh cd n SF, img_env VAL A_LIM (h_E regs sh cd n SF).
Proof. intros. unfold h_E. apply Eimg_env. Qed.
Lemma h_entry : forall (W : world SEGS) regs mem pc bx (mf SF sh cd n : Z),
  getr regs 2 = w64 mf -> getr regs 9 = w64 mf -> getr regs 20 = w64 (SF + 496) ->
  ew (h_E regs sh cd n SF) bx = Z_to_bv 64 h_SB ->
  alloc_ceiling + 16384 <= mf -> mf + 320 <= 2 ^ 47 -> mf mod 32 = 0 ->
  4096 <= SF -> SF + 1024 <= alloc_ceiling -> SF mod 64 = 0 -> in_app SF 1024 -> sh = SHADOW_OFF + SF / 8 ->
  1 <= n <= 6 -> 0 <= cd < 2 ^ 64 ->
  val_mem SEGS (rd W mem) (mf + 80) 8 SF -> val_mem SEGS (rd W mem) (mf + 144) 8 cd ->
  val_mem SEGS (rd W mem) (mf + 176) 8 SHADOW_OFF -> val_mem SEGS (rd W mem) (mf + 208) 8 n ->
  aview SEGS (w_H W) mem (sh + 62) = Some 0 ->
  (forall a, mf + 208 <= a < mf + 216 -> apresent (w_H W) mem a) ->
  apresent (w_H W) mem (SF + 496 + n) ->
  st_ok_pi SEGS VAL (h_E regs sh cd n SF) (mkSS pc sr_atoms [h_mf; h_n; h_sh; h_dot] None (h_facts bx))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc bx mf SF sh cd n R2 R9 R20 Hbx Hmf0 Hmf1 Hmf32 HSF0 HSF1 HSF64 HSFa Esh Hn Hcd V80 V144 V176 V208
  Hsh Hpn Hpd.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HSFa.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := h_E regs sh cd n SF) in *.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
  by (intros k r Hk; unfold E, h_E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (Hsh0 : 2147450880 <= sh /\ sh + 128 <= alloc_ceiling) by (rewrite Esh; unfold SHADOW_OFF; lia).
assert (U2 : bv_unsigned (ew E 2) = mf) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = mf) by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = SF + 496) by (rewrite (EE 20%nat 20%bv eq_refl), R20; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = h_SB).
{ unfold E, h_E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra regs _ 0). apply unsigned_lit_small. unfold h_SB. lia. }
assert (U33 : bv_unsigned (ew E 33) = sh + 62).
{ unfold E, h_E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra regs _ 1). apply unsigned_lit_small. lia. }
assert (U34 : bv_unsigned (ew E 34) = cd).
{ unfold E, h_E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra regs _ 2). apply unsigned_lit_small. lia. }
assert (U35 : bv_unsigned (ew E 35) = n).
{ unfold E, h_E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra regs _ 3). apply unsigned_lit_small. lia. }
assert (U36 : bv_unsigned (ew E 36) = SF + 496 + n).
{ unfold E, h_E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra regs _ 4). apply unsigned_lit_small. lia. }
assert (Ubx : bv_unsigned (ew E bx) = h_SB) by (rewrite Hbx; apply unsigned_lit_small; unfold h_SB; lia).
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold E, h_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
  + unfold h_mf, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor; [|constructor]]].
    * apply (chunk_ok_val SEGS E _ mf 80 8 (SOff 20 (-496)) SF); [|lia|lia|exact V80].
      cbn [sv_denot]. rewrite U20. f_equal. lia.
    * apply (chunk_ok_val SEGS E _ mf 144 8 (SOff 34 0) cd); [|lia|lia|exact V144].
      cbn [sv_denot]. rewrite U34, Z.add_0_r. reflexivity.
    * apply (chunk_ok_val SEGS E _ mf 176 8 (SOff 32 0) SHADOW_OFF); [|unfold SHADOW_OFF; lia|lia|exact V176].
      cbn [sv_denot]. rewrite U32, Z.add_0_r. reflexivity.
  + unfold h_n, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; apply (apresent_writable SEGS); apply Hpn; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ mf 208 8 (SOff 35 0) n); [|lia|lia|exact V208].
    cbn [sv_denot]. rewrite U35, Z.add_0_r. reflexivity.
  + unfold h_sh, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (sh + 62) 0 1 (SLit 0) 0); [reflexivity|lia|lia|].
    rewrite Z.add_0_r. apply h_vm1. exact Hsh.
  + unfold h_dot, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U36. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. replace (SF + 496 + n + o) with (SF + 496 + n) by lia. apply (apresent_writable SEGS). exact Hpd.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, h_mf, h_n, h_sh, h_dot.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U33, U36.
  pose proof Esh as Esh'. unfold SHADOW_OFF in Esh'. repeat split; try exact I; lia.
- unfold facts_ok, h_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok.
  cbn [af_lo af_hi af_al2]. rewrite U2, U9, U20, U32, U33, U35, U36. unfold h_SB.
  pose proof Esh as Esh2. unfold SHADOW_OFF in Esh2.
  split; [repeat split; lia|]. split; [exact I|]. split; [|split; [|exact I]].
  + apply U_inj. rewrite U_SAlu, !U_SOff, U20, U35, U36. cbn [zalu_raw]. unfold zcanon, M64. rewrite !Z.mod_small by lia.
    lia.
  + apply U_inj. rewrite U_SAlu, U_srl3, !U_SOff, U36, U33, Ubx. cbn [zalu_raw]. unfold zcanon, M64, h_SB.
    rewrite !Z.mod_small by lia. rewrite Esh. unfold SHADOW_OFF. lia.
Qed.
(* the caller lets a callee write bytes of its own frame (4, pos), or of its stack window above sp *)
Lemma h_twr_frame : forall STK sp0 FP ly S W0 mem md lyc Sc W memc mdc k sp pos q n,
  ajournal SEGS B STK sp0 FP ly S W0 mem md [(4, pos)] lyc Sc W memc mdc k ->
  frame_addr lyc 4 pos <= q -> q + n <= frame_addr lyc 4 pos + 1024 -> alloc_ceiling <= sp - ESTACK ->
  twr_ok B STK sp0 FP ly S lyc Sc [(4, pos)] W memc sp q n.
Proof.
intros STK sp0 FP ly S W0 mem md lyc Sc W memc mdc k sp pos q n HJ H1 H2 Hsp a Ha.
assert (Hw : awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc [(4, pos)] a).
{ right; right; right. exists 4, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
  change (fs_frame_bytes 4) with 1024. lia. }
destruct (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as [Hp Ho].
pose proof HJ as (HAR & _). pose proof (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos HAR) as Fb.
split; [exact Hw|]. split; [exact Hp|]. split; [exact Ho|].
pose proof asan_consts as (C1 & _).
assert (Hin : In (4, pos) (frames Sc)) by (pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _); rewrite Hfrs; left; reflexivity).
destruct (Fb Hin) as (_ & F1 & _). change (fs_frame_bytes 4) with 1024 in F1. lia.
Qed.
Lemma h_twr_stack : forall STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k sp q n,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
  sp0 - STK <= q -> q + n <= sp0 -> sp <= q ->
  twr_ok B STK sp0 FP ly S lyc Sc own W memc sp q n.
Proof.
intros STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k sp q n HJ H1 H2 H3 a Ha.
assert (Hw : awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) by (left; lia).
destruct (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as [Hp Ho].
split; [exact Hw|]. split; [exact Hp|]. split; [exact Ho | lia].
Qed.

Lemma h_blt : forall E n v, ew E n = Z_to_bv 64 v -> - 2 ^ 31 <= v < 2 ^ 31 ->
  branch_taken BC_LT (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (v <? 0).
Proof.
intros E n v H Hv. rewrite YO0c.branch_lt.
change (bv_unsigned (sv_denot E (SOff n 0))) with (U E (SOff n 0)). change (bv_unsigned (sv_denot E (SLit 0))) with (U E (SLit 0)).
rewrite U_SOff, U_SLit, H, Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap, YO0b.s64. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.add_0_r, Z.mod_mod by lia. change (0 mod 2 ^ 64) with 0. change (0 <? 2 ^ 63) with true.
destruct (Z.ltb_spec v 0) as [Hn | Hp].
- replace (v mod 2 ^ 64) with (v + 2 ^ 64) by (apply Z.mod_unique with (-1); lia).
  destruct (Z.ltb_spec (v + 2 ^ 64) (2 ^ 63)); [lia|]. apply Z.ltb_lt. lia.
- rewrite Z.mod_small by lia. destruct (Z.ltb_spec v (2 ^ 63)); [|lia]. apply Z.ltb_ge. lia.
Qed.
Ltac h_pres0 HP :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hq := fresh "Hq" in
  intros r Hr; pose proof (HP (bv_unsigned r)) as Hq; rewrite Z_to_bv_bv_unsigned in Hq; apply Hq;
  cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [lazymatch goal with |- acallee_saved (bv_unsigned ?x) => let v := eval vm_compute in (bv_unsigned x) in
       change (bv_unsigned x) with v end; unfold acallee_saved; lia |]);
  destruct Hr.

Ltac h_pres HKR HP :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hq := fresh "Hq" in
  intros r Hr; rewrite <- (HKR r) by (cbn [In] in Hr |- *; tauto);
  pose proof (HP (bv_unsigned r)) as Hq; rewrite Z_to_bv_bv_unsigned in Hq; apply Hq;
  cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [lazymatch goal with |- acallee_saved (bv_unsigned ?x) => let v := eval vm_compute in (bv_unsigned x) in
       change (bv_unsigned x) with v end; unfold acallee_saved; lia |]);
  destruct Hr.

Theorem seg_H_holds :
  seg_H B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
    arodata_okS.
Proof.
intros g pos mf W2 c2 Hstart.
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & Rs3 & V80 & V192 & V176 & Vra & Vs0 &
  V24 & V32 & V40 & V48 & V56 & V64 & V72 & V80b & V88 & V96 & V104 & Vmf24 & Vflag & HPRE & Hfds & Hfs & Hinb).
destruct HP as ((Hidb & Hidz & Hidk) & Hbl & Hid3 & Hmid & Hzf & Hzef & Vn & V136 & V144 & V160 & V168 &
  R10 & R20 & R11 & R13 & R12 & R18 & R21 & R23 & R24 & R26).
unfold V_ef, N_ef, V_f, N_f, M_n1 in *.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
(* the entry state *)
pose proof HPRE as (HFN & Hraz & _ & _ & Hinp & Hlen & _ & _ & Hnev0 & _).
(* the journal at the start *)
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & Hnev2 & _ & _ & _ & _ & _ & _ & Hpres2 & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
set (sp0 := e_sp0 g) in *.
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
set (SF := SFa g pos) in *.
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF0 & HSF1 & HSFapp).
destruct (frame_al64 SEGS B ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF64 & _ & _).
rewrite EFa in HSF0, HSF1, HSFapp, HSF64. rewrite HFB in HSF1, HSFapp.
set (sh := shadow_addr SF) in *.
assert (Esh : sh = SHADOW_OFF + SF / 8) by reflexivity.
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
assert (Hsh1 : 2147450880 <= sh /\ sh + 128 <= alloc_ceiling).
{ clear - Esh HSF0 HSF1 C1. clearbody sh SF. unfold SHADOW_OFF in Esh. lia. }
assert (Hshf58 : shadow_addr (SF + 464) = sh + 58).
{ unfold shadow_addr. rewrite Esh. clear - HSF64. unfold SHADOW_OFF. lia. }
assert (Hshef : shadow_addr (SF + 496) = sh + 62).
{ unfold shadow_addr. rewrite Esh. clear - HSF64. unfold SHADOW_OFF. lia. }
(* the model *)
set (inp := e_pl g) in *.
set (fw := SlotModel.t_any_fw inp) in *.
assert (Hfw : 0 <= fw < 65536).
{ unfold fw, SlotModel.t_any_fw, SlotModel.tb.
  pose proof (SlotModel.inb_range inp (SlotModel.cT inp + 9)). pose proof (SlotModel.inb_range inp (SlotModel.cT inp + 10)).
  lia. }
pose proof (reac_identity_fw_str_c.reac_identity_fw_str_c3_len fw Hfw) as [HL1 HL2].
set (v1 := fw / 1000) in *. set (v2 := fw mod 1000) in *.
set (n1 := put_dec_c.dec_len v1 1).
assert (Hn1 : reac_identity_fw_str_c.L fw = n1 + 4) by (unfold n1, put_dec_c.dec_len; lia).
assert (Hn1r : 1 <= n1 <= 2) by (clear - Hn1 HL2; destruct (fw <? 10000); lia).
assert (Hv2 : 0 <= v2 < 1000) by (unfold v2; apply Z.mod_pos_bound; lia).
assert (Hn2 : put_dec_c.dec_len v2 3 = 3).
{ unfold put_dec_c.dec_len. rewrite (reac_identity_fw_str_c.reac_identity_fw_str_dec_f v2 Hv2). reflexivity. }
assert (Hv1 : 0 <= v1 < 66) by (unfold v1; clear - Hfw; lia).
set (K := 4 * Z.of_nat (m_nrec g) + 4) in *.
(* what the segment may write: the callees' stack windows below sp = mf, the counter slot, f and ef *)
pose (WR0 := fun a : Z => mf - 8192 <= a < mf \/ mf + 208 <= a < mf + 216 \/ SF + 464 <= a < SF + 472 \/
  SF + 496 <= a < SF + 512).
assert (HshSF : sh + 128 <= SF \/ SF + 1024 <= sh).
{ pose proof HSFapp as Hap. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hap.
  pose proof Esh as Esh'. unfold SHADOW_OFF in Esh'. clear - Hap Esh' HSF0 HSF1 C1. lia. }
assert (HshWR : forall a, sh <= a < sh + 128 -> ~ WR0 a).
{ intros a Ha Hw. unfold WR0 in Hw. pose proof HSFapp as Hap. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hap.
  clear - Ha Hw Hap Esh Hsh1 Hmf0 C1 HSF0 HSF1. unfold SHADOW_OFF in Esh. lia. }
(* the addresses whose bytes the boundaries speak of *)
pose (CL := fun a : Z => alloc_ceiling <= a \/ SF <= a < SF + 1024 \/ sh <= a < sh + 128 \/
  exists b n j, In (b, n) (ablocks B ly2 S2) /\ 0 <= j < req_size n /\ a = b + j).
(* ---- 0x817bc: the call of put_dec ---- *)
remember (Eimg (Ereg regs2 [])) as E0 eqn:HE0.
assert (HEI0 : img_env VAL A_LIM E0) by (rewrite HE0; apply Eimg_env).
assert (EE0 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = getr regs2 r)
  by (intros n r Hn; rewrite HE0; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ER0 : regs_ok E0 sr_atoms regs2) by (rewrite HE0; apply regs_ok_Eimg_Ereg).
assert (AGE0 : env_agree 32 (Ereg regs2 []) E0)
  by (rewrite HE0; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE0.
assert (HS : st_ok_pi SEGS VAL E0 ss_h0
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x10b0)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_h0. apply pa_entry_st_ok_full;
  [exact ER0 | vm_compute; reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
unfold cfg_at. change (w64 (BASE + 0x10b0)) with (Z_to_bv 64 (BASE + 0x10b0)).
paj_run_shc RUNP RUNC HS HJ.
{ apply awr_ok_nil. }
assert (K0 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. apply (kept_of_frame E0 _ (w_H W2) mem2 (ms_mem ms) (fun _ => False) HFr); [|exact Ha|intros []].
  intros bb wlo whi aa Hin _. cbn in Hin. destruct Hin. }
clear HF HFr HG.
prreg HS (1%bv : bv 5) Q1.
pose proof (regs_kept_of_st_ok SEGS E0 _ (restrict (w_H W2) ms) regs2 []
  [2; 3; 4; 8; 9; 10; 11; 12; 13; 18; 19; 20; 21; 23; 24; 26]%bv HS AGE0 ltac:(vm_compute; reflexivity)) as HKR.
cbn [ms_regs restrict] in HKR.
pmkst HS. rewrite (PSIG IS_put_dec AF_put_dec eq_refl).
assert (Usp : spZ (ms_regs ms) = mf).
{ unfold spZ. rewrite (HKR 2%bv ltac:(cbn; tauto)), Rsp. unfold w64. apply unsigned_lit_small. clear - Hmf0 Hmfb Hshi H47 C1. lia. }
eapply SRr_bind.
{ apply (HPD LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 W2 (ms_mem ms) _ K
    (ms_regs ms) (SF + 496) (mf + 208) 0 v1 1 HJ).
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1, unsigned_lit_small by lia. clear - HBLO. lia.
  - rewrite (HKR 3%bv ltac:(cbn; tauto)). exact Rgp.
  - rewrite (HKR 4%bv ltac:(cbn; tauto)). exact Rtp.
  - rewrite (HKR 10%bv ltac:(cbn; tauto)). exact R10.
  - rewrite (HKR 11%bv ltac:(cbn; tauto)). exact R11.
  - rewrite (HKR 12%bv ltac:(cbn; tauto)), R12. unfold w64. rewrite unsigned_lit_small by lia. apply Z.mod_small. lia.
  - left. rewrite (HKR 12%bv ltac:(cbn; tauto)), R12. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - rewrite (HKR 13%bv ltac:(cbn; tauto)). exact R13.
  - lia.
  - rewrite Usp. exact Hmf32.
  - rewrite Usp. unfold PUT_DEC_STK, ESTACK. clear - Hmfb HSTK' Has. lia.
  - rewrite Usp. clear - Hmfb. lia.
  - rewrite Hfrs. cbn. lia.
  - clear - Hmf32. lia.
  - clear - HSF0. lia.
  - lia.
  - apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms) (mf + 208) (mf + 208) 8 0); [|exact Vn].
    intros kk Hkk. apply K0. clear - Hkk Hmf0 Hmfb Hshi H47 C1. lia.
  - rewrite Usp. eapply h_twr_stack; [exact HJ | | | ]; clear - Hmfb HSTK' Has; lia.
  - rewrite Usp. eapply h_twr_frame; [exact HJ | | | ]; rewrite ?EFa; unfold n1 in *; clear - Hn1r HSF1 HSF0 Hmf0 Hes; lia.
  - rewrite Usp. eapply h_tsrc_stack; [exact HJ | | | | ]; clear - Hmfb HSTK' Has; lia.
  - rewrite Usp. eapply (h_tsrc_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 4 pos (SF + 496) 16); [exact HJ | exact Hin4 | ..];
      rewrite ?EFa, ?HFB; try (unfold n1 in *; clear - HSF64 HSF1 HSF0 Hn1r Hmf0 Hes; lia).
    apply (h_zs_moved (aview SEGS (w_H W2) mem2)); [|exact Hzef].
    intros i Hi. apply K0. unfold shadow_of_addr. clear - Hi Hsh1 Esh HSF64 HSF0 HSF1 C1. unfold SHADOW_OFF in *. lia.
  - right. clear - Hn1r HSF1 Hmf0. unfold n1 in *. lia.
  - rewrite Usp. left. lia.
  - rewrite Usp. right. unfold PUT_DEC_STK, ESTACK. clear - Hn1r HSF1 Hmf0. unfold n1 in *. lia.
  - unfold EV_PUT_DEC. clear - Hnev2 Hnev0 HEV Hk. lia. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hfrs3 & Hbl3 & HK3 & HD3 & HN3).
rewrite Q1. unfold EV_PUT_DEC in HJ3. rewrite Z.add_0_r in HJ3.
(* ---- back at 0x817c0: what the call kept ---- *)
pose proof HJ3 as (HAR3 & Hly3 & _ & _ & _ & _ & Hnev3 & _ & _ & _ & _ & _ & _ & Hpres3 & _).
pose proof Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
assert (EFa3 : frame_addr ly3 4 pos = SF) by (change SF with (SFa g pos); unfold SFa, frame_addr; rewrite EF3; reflexivity).
rewrite Hfrs in Hfrs3.
assert (KP1 : forall a, 0 <= a < 2 ^ 64 -> CL a -> ~ WR0 a -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hc Hw. rewrite <- (K0 a Ha).
  apply (h_keep_tcj PUT_DEC_STK ly2 S2 W2 (ms_mem ms) W3 mem3 (spZ (ms_regs ms)) _ (ablocks B ly2 S2) pos SF WR0
    HK3 Hfrs EFa (fun b n H => H)); [ | | exact Ha | exact Hc | exact Hw].
  - intros x Hx. rewrite Usp in Hx. unfold WR0. left. unfold PUT_DEC_STK, ESTACK in Hx. lia.
  - intros x Hx. unfold WR0. cbn beta in Hx. clear - Hx Hn1r. unfold n1 in *. lia. }
assert (P3 : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 26]%bv -> getr regs3 r = getr regs2 r).
{ h_pres HKR HP3. }
clear HKR HS K0 Usp Q1 HP3 HK3 HJ ms.
set (cd := SlotModel.t_cap_disp inp) in *.
assert (Hcd : 0 <= cd < 64) by (unfold cd, SlotModel.t_cap_disp; apply Z.mod_pos_bound; lia).
assert (Hmf47 : mf + 320 <= 2 ^ 47) by (clear - Hmfb Hshi Hsp0al H47; lia).
assert (Hsh62 : aview SEGS (w_H W2) mem2 (sh + 62) = Some 0).
{ pose proof (Hzef 0 ltac:(lia)) as Z0. unfold shadow_of_addr in Z0. rewrite Z.add_0_r in Z0.
  change (SHADOW_OFF + (SF + 496) / 8) with (shadow_addr (SF + 496)) in Z0. rewrite Hshef in Z0. exact Z0. }
(* ---- run 1: 0x817c0 .. the call of put_dec at 0x8180c ---- *)
assert (HS : st_ok_pi SEGS VAL (h_E regs3 sh cd n1 SF) ss_h1
  (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + 0x10b4)) mem3 (seg_rom SEGS)))).
{ unfold ss_h1. apply (h_entry W3 regs3 mem3 0x10b4 32 mf SF sh cd n1).
  - rewrite P3 by (cbn; tauto). exact Rsp.
  - rewrite P3 by (cbn; tauto). exact Rs1.
  - rewrite P3 by (cbn; tauto). exact R20.
  - exact (proj1 (h_E_ext regs3 sh cd n1 SF)).
  - exact Hmf0. - exact Hmf47. - exact Hmf32. - exact HSF0. - exact HSF1. - exact HSF64. - exact HSFapp. - exact Esh.
  - unfold n1 in *. lia. - lia.
  - apply (val_mem_moved SEGS (w_H W2) (w_H W3) mem2 mem3 (mf + 80) (mf + 80) 8 SF); [|exact V80].
    intros kk Hkk. apply KP1; [lia | left; lia | unfold WR0; lia].
  - apply (val_mem_moved SEGS (w_H W2) (w_H W3) mem2 mem3 (mf + 144) (mf + 144) 8 cd); [|exact V144].
    intros kk Hkk. apply KP1; [lia | left; lia | unfold WR0; lia].
  - apply (val_mem_moved SEGS (w_H W2) (w_H W3) mem2 mem3 (mf + 176) (mf + 176) 8 SHADOW_OFF); [|exact V176].
    intros kk Hkk. apply KP1; [lia | left; lia | unfold WR0; lia].
  - replace n1 with (0 + put_dec_c.dec_len v1 1) by (unfold n1; lia). exact HN3.
  - rewrite (KP1 (sh + 62)); [exact Hsh62 | clear - Hsh1 C1; lia | right; right; left; lia | apply HshWR; lia].
  - intros a Ha. apply Hpres3. clear - Ha Hmfb Hmf0 HSTK' Has. lia.
  - destruct (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SF + 496 + n1) HJ3) as [Hp _]; [|exact Hp].
    right; right; right. exists 4, pos. split; [left; reflexivity|]. left. unfold in_zr; cbn [fst snd].
    rewrite EFa3, HFB. unfold n1 in *. lia. }
pose proof (h_E_ext regs3 sh cd n1 SF) as (E1x32 & E1x33 & E1x34 & E1x35 & E1x36).
pose proof (h_E_reg regs3 sh cd n1 SF) as EE1. pose proof (h_E_agree regs3 sh cd n1 SF) as AGE1.
pose proof (h_E_img regs3 sh cd n1 SF) as HEI1.
remember (h_E regs3 sh cd n1 SF) as E1 eqn:HE1. clear HE1.
assert (U1_9 : bv_unsigned (ew E1 9) = mf).
{ rewrite (EE1 9%nat 9%bv eq_refl), P3, Rs1 by (cbn; tauto). apply unsigned_lit_small. lia. }
assert (U1_36 : bv_unsigned (ew E1 36) = SF + 496 + n1) by (rewrite E1x36; apply unsigned_lit_small; unfold n1 in *; lia).
assert (U1_35 : bv_unsigned (ew E1 35) = n1) by (rewrite E1x35; apply unsigned_lit_small; unfold n1 in *; lia).
paj_run_shc RUNP RUNC HS HJ3.
{ intros a (r & Hr & Ha). cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | []]]]]; unfold h_mf, h_n, h_sh, h_dot in Ha;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; [lia | | lia | ].
  - left. rewrite U1_9 in Ha. clear - Ha Hmfb HSTK' Has. lia.
  - right; right; right. exists 4, pos. split; [left; reflexivity|]. left. unfold in_zr; cbn [fst snd].
    rewrite U1_36 in Ha. rewrite EFa3, HFB. unfold n1 in *. lia. }
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 208 <= a < mf + 216) -> a <> SF + 496 + n1 ->
  aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hw1 Hw2.
  apply (kept_of_frame E1 _ (w_H W3) mem3 (ms_mem ms) (fun x => mf + 208 <= x < mf + 216 \/ x = SF + 496 + n1) HFr);
  [|exact Ha| intros [H|H]; [exact (Hw1 H) | exact (Hw2 H)]].
  intros bb wlo whi aa Hin Hr. unfold windows in Hin. cbn in Hin.
  destruct Hin as [Eq | [Eq | [Eq | [Eq | []]]]]; injection Eq as <- <- <-; cbn [base_val] in Hr;
  first [lia | rewrite U1_9 in Hr; left; lia | rewrite U1_36 in Hr; right; lia]. }
clear HF HFr HG.
pose proof (h_val_of_st_ok _ _ _ (YP09.mkRegion (Some 9%nat) 208 216 208 216 [YP09.mkChunk 208 (CVal 8 (SOff 35 1))])
  9%nat 208 8 (SOff 35 1) (n1 + 1) HS ltac:(cbn [ss_mem setpc In]; repeat (first [left; reflexivity | right]))
  eq_refl ltac:(cbn [In]; left; reflexivity)) as VN1.
specialize (VN1 ltac:(cbn [sv_denot]; rewrite U1_35; reflexivity) ltac:(unfold n1 in *; lia) ltac:(lia)).
rewrite U1_9 in VN1. cbn [ms_mem restrict] in VN1.
pose proof (h_val_of_st_ok _ _ _ (YP09.mkRegion (Some 36%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 46))])
  36%nat 0 1 (SLit 46) 46 HS ltac:(cbn [ss_mem setpc In]; repeat (first [left; reflexivity | right]))
  eq_refl ltac:(cbn [In]; left; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as VD1.
rewrite U1_36, Z.add_0_r in VD1. cbn [ms_mem restrict] in VD1.
apply aview_of_val_mem1 in VD1; [|lia].
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (13%bv : bv 5) Q13.
prreg HS (25%bv : bv 5) Q25. prreg_raw HS (12%bv : bv 5) Q12.
pose proof (regs_kept_of_st_ok SEGS E1 _ (restrict (w_H W3) ms) regs3 _
  [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 26]%bv HS AGE1 ltac:(vm_compute; reflexivity)) as HKR.
cbn [ms_regs restrict] in HKR.
pmkst HS. rewrite (PSIG IS_put_dec AF_put_dec eq_refl).
assert (Esh496 : shadow_of_addr SHADOW_OFF (SF + 496) = sh + 62)
  by (change (shadow_of_addr SHADOW_OFF (SF + 496)) with (shadow_addr (SF + 496)); exact Hshef).
assert (Usp : spZ (ms_regs ms) = mf).
{ unfold spZ. rewrite (HKR 2%bv ltac:(cbn; tauto)), (P3 2%bv ltac:(cbn; tauto)), Rsp.
  unfold w64. apply unsigned_lit_small. lia. }
assert (Hz1 : zero_shadow (aview SEGS (w_H W3) (ms_mem ms)) SHADOW_OFF (SF + 496) 16).
{ apply (h_zs_moved (aview SEGS (w_H W2) mem2)); [|exact Hzef].
  intros i Hi. rewrite Esh496. rewrite KR1 by (clear - Hi Hsh1 C1 Hmf0 HSF0 HSF1 Hn1r HshSF; unfold n1 in *; lia).
  apply KP1; [clear - Hi Hsh1 C1; lia | right; right; left; lia | apply HshWR; lia]. }
assert (E1_21 : ew E1 21 = Z_to_bv 64 fw)
  by (rewrite (EE1 21%nat 21%bv eq_refl), (P3 21%bv ltac:(cbn; tauto)), R21; reflexivity).
assert (E1_18 : ew E1 18 = Z_to_bv 64 v1)
  by (rewrite (EE1 18%nat 18%bv eq_refl), (P3 18%bv ltac:(cbn; tauto)), R18; reflexivity).
pose proof (h_m1000 E1 fw E1_21 E1_18 Hfw) as Hm1000. unfold h_M1000 in Hm1000.
(* ---- 0x8180c: the second call of put_dec ---- *)
eapply SRr_bind.
{ apply (HPD LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly3 S3 W3 (ms_mem ms) _ K
    (ms_regs ms) (SF + 496) (mf + 208) (n1 + 1) v2 3 HJ3).
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1, unsigned_lit_small by lia. clear - HBLO. lia.
  - rewrite (HKR 3%bv ltac:(cbn; tauto)), (P3 3%bv ltac:(cbn; tauto)). exact Rgp.
  - rewrite (HKR 4%bv ltac:(cbn; tauto)), (P3 4%bv ltac:(cbn; tauto)). exact Rtp.
  - rewrite Q10, (EE1 20%nat 20%bv eq_refl), (P3 20%bv ltac:(cbn; tauto)). exact R20.
  - rewrite Q11, U1_9. reflexivity.
  - rewrite Q12, Hm1000. rewrite unsigned_lit_small by lia. apply Z.mod_small. lia.
  - left. rewrite Q12, Hm1000. rewrite unsigned_lit_small by lia. lia.
  - rewrite Q13. reflexivity.
  - lia.
  - rewrite Usp. exact Hmf32.
  - rewrite Usp. unfold PUT_DEC_STK, ESTACK. clear - Hmfb HSTK' Has. lia.
  - rewrite Usp. clear - Hmfb. lia.
  - rewrite Hfrs3. cbn. lia.
  - clear - Hmf32. lia.
  - clear - HSF0. lia.
  - unfold n1 in *. lia.
  - exact VN1.
  - rewrite Usp. eapply h_twr_stack; [exact HJ3 | | | ]; clear - Hmfb HSTK' Has; lia.
  - rewrite Usp. eapply h_twr_frame; [exact HJ3 | | | ]; rewrite ?EFa3, ?Hn2;
      clear - Hn1r HSF1 HSF0 Hmf0 Hes Hn2; unfold n1 in *; lia.
  - rewrite Usp. eapply h_tsrc_stack; [exact HJ3 | | | | ]; clear - Hmfb HSTK' Has; lia.
  - rewrite Usp. rewrite Hn2.
    eapply (h_tsrc_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 4 pos (SF + 496) 16); [exact HJ3 | | ..];
      rewrite ?EFa3, ?HFB; try (unfold n1 in *; clear - HSF64 HSF1 HSF0 Hn1r Hmf0 Hes; lia).
    + rewrite Hfrs3. left. reflexivity.
    + exact Hz1.
  - rewrite Hn2. right. clear - Hn1r HSF1 Hmf0. unfold n1 in *. lia.
  - rewrite Usp. left. lia.
  - rewrite Usp, Hn2. right. unfold PUT_DEC_STK, ESTACK. clear - Hn1r HSF1 Hmf0. unfold n1 in *. lia.
  - unfold EV_PUT_DEC. clear - Hnev3 Hnev0 HEV Hk. lia. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hfrs4 & Hbl4 & HK4 & HD4 & HN4).
rewrite Q1. unfold EV_PUT_DEC in HJ4. rewrite Z.add_0_r in HJ4. rewrite Hn2 in HN4.
(* ---- back at 0x81810 ---- *)
set (n2 := n1 + 4) in *.
pose proof HJ4 as (HAR4 & Hly4 & _ & _ & _ & _ & Hnev4 & _ & _ & _ & _ & _ & _ & Hpres4 & _).
pose proof Hly4 as (_ & _ & _ & _ & _ & EF4 & _).
assert (EFa4 : frame_addr ly4 4 pos = SF) by (change SF with (SFa g pos); unfold SFa, frame_addr; rewrite EF4; reflexivity).
rewrite Hfrs3 in Hfrs4.
assert (P4ms : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr regs4 r = getr (ms_regs ms) r) by (h_pres0 HP4).
assert (P4 : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 26]%bv -> getr regs4 r = getr regs2 r).
{ intros r Hr. rewrite (P4ms r ltac:(cbn [In] in Hr |- *; tauto)), (HKR r Hr). exact (P3 r Hr). }
assert (R25_4 : getr regs4 25 = Z_to_bv 64 h_SB)
  by (rewrite (P4ms 25%bv ltac:(cbn; tauto)), Q25; exact E1x32).
assert (KQ2 : forall a, 0 <= a < 2 ^ 64 -> CL a -> ~ WR0 a -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hc Hw.
  rewrite (h_keep_tcj PUT_DEC_STK ly3 S3 W3 (ms_mem ms) W4 mem4 (spZ (ms_regs ms)) _ (ablocks B ly2 S2) pos SF WR0
    HK4 Hfrs3 EFa3 ltac:(intros b n Hb; rewrite Hbl3; exact Hb)
    ltac:(intros x Hx; rewrite Usp in Hx; unfold WR0; unfold PUT_DEC_STK, ESTACK in Hx; left; lia)
    ltac:(intros x Hx; cbn beta in Hx; unfold WR0; clear - Hx Hn1r Hn2; unfold n1 in *; lia) a Ha Hc Hw).
  rewrite KR1 by (unfold WR0 in Hw; clear - Ha Hw Hn1r; unfold n1 in *; lia). exact (KP1 a Ha Hc Hw). }
assert (Hz2 : zero_shadow (aview SEGS (w_H W4) mem4) SHADOW_OFF (SF + 496) 16).
{ apply (h_zs_moved (aview SEGS (w_H W2) mem2)); [|exact Hzef].
  intros i Hi. rewrite Esh496. apply KQ2; [clear - Hi Hsh1 C1; lia | right; right; left; lia | apply HshWR; lia]. }
assert (Hzf2 : zero_shadow (aview SEGS (w_H W4) mem4) SHADOW_OFF (SF + 464) 8).
{ apply (h_zs_moved (aview SEGS (w_H W2) mem2)); [|exact Hzf].
  intros i Hi. change (shadow_of_addr SHADOW_OFF (SF + 464)) with (shadow_addr (SF + 464)). rewrite Hshf58.
  apply KQ2; [clear - Hi Hsh1 C1; lia | right; right; left; clear - Hi Hsh1; lia | apply HshWR; clear - Hi Hsh1; lia]. }
assert (Hlen1 : Z.of_nat (length (IdentSpec.DEC v1 1)) = n1) by (unfold n1, put_dec_c.dec_len; reflexivity).
assert (Hn2' : length (IdentSpec.DEC v2 3) = 3%nat)
  by (pose proof Hn2 as Hq; unfold put_dec_c.dec_len in Hq; lia).
assert (Hlen1' : length (IdentSpec.DEC v1 1) = Z.to_nat n1) by (clear - Hlen1; lia).
assert (Hn2'' : length (IdentSpec.DEC v2 3) = 3%nat) by exact Hn2'.
assert (HWR2 : forall a, 0 <= a < 2 ^ 64 -> CL a ->
  ~ (mf - 8192 <= a < mf \/ mf + 208 <= a < mf + 216 \/ SF + 496 + n1 + 1 <= a < SF + 512) ->
  aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) (ms_mem ms) a).
{ intros a Ha Hc Hw.
  apply (h_keep_tcj PUT_DEC_STK ly3 S3 W3 (ms_mem ms) W4 mem4 (spZ (ms_regs ms)) _ (ablocks B ly2 S2) pos SF
    (fun x => mf - 8192 <= x < mf \/ mf + 208 <= x < mf + 216 \/ SF + 496 + n1 + 1 <= x < SF + 512)
    HK4 Hfrs3 EFa3 ltac:(intros b n Hb; rewrite Hbl3; exact Hb)
    ltac:(intros x Hx; rewrite Usp in Hx; unfold PUT_DEC_STK, ESTACK in Hx; left; lia)
    ltac:(intros x Hx; cbn beta in Hx; rewrite Hn2 in Hx; right; unfold n1 in *; lia));
  [exact Ha | exact Hc | exact Hw]. }
assert (VD1_4 : aview SEGS (w_H W4) mem4 (SF + 496 + n1) = Some 46).
{ rewrite HWR2; [exact VD1 | unfold n1 in *; lia | right; left; unfold n1 in *; lia | unfold n1 in *; lia]. }
assert (HD3_4 : garr8 SEGS (rd W4 mem4) (SF + 496) (map bv_unsigned (IdentSpec.DEC v1 1))).
{ apply (h_garr8_moved (w_H W3) (w_H W4) mem3 mem4); [|rewrite Z.add_0_r in HD3; exact HD3].
  intros j Hj. rewrite length_map in Hj. rewrite Hlen1 in Hj.
  rewrite HWR2; [| unfold n1 in *; lia | right; left; unfold n1 in *; lia | unfold n1 in *; lia].
  apply KR1; unfold n1 in *; lia. }
clear HKR HS KR1 KP1 Usp Q1 Q10 Q11 Q12 Q13 Q25 HP4 HK4 HJ3 HD3 VN1 VD1 Hz1 Hm1000 E1_21 E1_18 P4ms HWR2 ms.
(* ---- run 2: 0x81810 .. the call of reac_identity_fw_str at 0x81844 ---- *)
assert (HS : st_ok_pi SEGS VAL (h_E regs4 sh cd n2 SF) ss_h2
  (restrict (w_H W4) (mkst regs4 (Z_to_bv 64 (BASE + 0x1104)) mem4 (seg_rom SEGS)))).
{ unfold ss_h2. apply (h_entry W4 regs4 mem4 0x1104 25 mf SF sh cd n2).
  - rewrite (P4 2%bv ltac:(cbn; tauto)). exact Rsp.
  - rewrite (P4 9%bv ltac:(cbn; tauto)). exact Rs1.
  - rewrite (P4 20%bv ltac:(cbn; tauto)). exact R20.
  - rewrite (h_E_reg regs4 sh cd n2 SF 25%nat 25%bv eq_refl). exact R25_4.
  - exact Hmf0. - exact Hmf47. - exact Hmf32. - exact HSF0. - exact HSF1. - exact HSF64. - exact HSFapp. - exact Esh.
  - unfold n2, n1 in *. lia. - lia.
  - apply (val_mem_moved SEGS (w_H W2) (w_H W4) mem2 mem4 (mf + 80) (mf + 80) 8 SF); [|exact V80].
    intros kk Hkk. apply KQ2; [lia | left; lia | unfold WR0; lia].
  - apply (val_mem_moved SEGS (w_H W2) (w_H W4) mem2 mem4 (mf + 144) (mf + 144) 8 cd); [|exact V144].
    intros kk Hkk. apply KQ2; [lia | left; lia | unfold WR0; lia].
  - apply (val_mem_moved SEGS (w_H W2) (w_H W4) mem2 mem4 (mf + 176) (mf + 176) 8 SHADOW_OFF); [|exact V176].
    intros kk Hkk. apply KQ2; [lia | left; lia | unfold WR0; lia].
  - replace n2 with (n1 + 1 + 3) by (unfold n2; lia). exact HN4.
  - pose proof (Hz2 0 ltac:(lia)) as Hz20. rewrite Esh496, Z.add_0_r in Hz20. exact Hz20.
  - intros a Ha. apply Hpres4. clear - Ha Hmfb Hmf0 HSTK' Has. lia.
  - destruct (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SF + 496 + n2) HJ4) as [Hp _]; [|exact Hp].
    right; right; right. exists 4, pos. split; [left; reflexivity|]. left. unfold in_zr; cbn [fst snd].
    rewrite EFa4, HFB. unfold n2, n1 in *. lia. }
pose proof (h_E_ext regs4 sh cd n2 SF) as (E2x32 & E2x33 & E2x34 & E2x35 & E2x36).
pose proof (h_E_reg regs4 sh cd n2 SF) as EE2. pose proof (h_E_agree regs4 sh cd n2 SF) as AGE2.
pose proof (h_E_img regs4 sh cd n2 SF) as HEI2.
remember (h_E regs4 sh cd n2 SF) as E2 eqn:HE2. clear HE2.
assert (U2_9 : bv_unsigned (ew E2 9) = mf).
{ rewrite (EE2 9%nat 9%bv eq_refl), (P4 9%bv ltac:(cbn; tauto)), Rs1. apply unsigned_lit_small. lia. }
assert (U2_20 : bv_unsigned (ew E2 20) = SF + 496).
{ rewrite (EE2 20%nat 20%bv eq_refl), (P4 20%bv ltac:(cbn; tauto)), R20. apply unsigned_lit_small. lia. }
assert (U2_36 : bv_unsigned (ew E2 36) = SF + 496 + n2)
  by (rewrite E2x36; apply unsigned_lit_small; unfold n2, n1 in *; lia).
assert (U2_35 : bv_unsigned (ew E2 35) = n2) by (rewrite E2x35; apply unsigned_lit_small; unfold n2, n1 in *; lia).
paj_run_shc RUNP RUNC HS HJ4.
{ intros a (r & Hr & Ha). cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | []]]]]; unfold h_mf, h_n, h_sh, h_dot in Ha;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; [lia | | lia | ].
  - left. rewrite U2_9 in Ha. clear - Ha Hmfb HSTK' Has. lia.
  - right; right; right. exists 4, pos. split; [left; reflexivity|]. left. unfold in_zr; cbn [fst snd].
    rewrite U2_36 in Ha. rewrite EFa4, HFB. unfold n2, n1 in *. lia. }
assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 208 <= a < mf + 216) -> a <> SF + 496 + n2 ->
  aview SEGS (w_H W4) (ms_mem ms) a = aview SEGS (w_H W4) mem4 a).
{ intros a Ha Hw1 Hw2.
  apply (kept_of_frame E2 _ (w_H W4) mem4 (ms_mem ms) (fun x => mf + 208 <= x < mf + 216 \/ x = SF + 496 + n2) HFr);
  [|exact Ha| intros [H|H]; [exact (Hw1 H) | exact (Hw2 H)]].
  intros bb wlo whi aa Hin Hr. unfold windows in Hin. cbn in Hin.
  destruct Hin as [Eq | [Eq | [Eq | [Eq | []]]]]; injection Eq as <- <- <-; cbn [base_val] in Hr;
  first [lia | rewrite U2_9 in Hr; left; lia | rewrite U2_36 in Hr; right; lia]. }
clear HF HFr HG.
pose proof (h_val_of_st_ok _ _ _ (YP09.mkRegion (Some 36%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 0))])
  36%nat 0 1 (SLit 0) 0 HS ltac:(cbn [ss_mem setpc In]; repeat (first [left; reflexivity | right]))
  eq_refl ltac:(cbn [In]; left; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as VD2.
rewrite U2_36, Z.add_0_r in VD2. cbn [ms_mem restrict] in VD2.
apply aview_of_val_mem1 in VD2; [|lia].
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (18%bv : bv 5) Q18. prreg HS (22%bv : bv 5) Q22. prreg HS (27%bv : bv 5) Q27.
pose proof (regs_kept_of_st_ok SEGS E2 _ (restrict (w_H W4) ms) regs4 _
  [2; 3; 4; 8; 9; 19; 20; 21; 23; 24; 25; 26]%bv HS AGE2 ltac:(vm_compute; reflexivity)) as HKR2.
cbn [ms_regs restrict] in HKR2.
pmkst HS. rewrite (PSIG IS_reac_identity_fw_str AF_reac_identity_fw_str eq_refl).
assert (Usp2 : spZ (ms_regs ms) = mf).
{ unfold spZ. rewrite (HKR2 2%bv ltac:(cbn; tauto)), (P4 2%bv ltac:(cbn; tauto)), Rsp.
  unfold w64. apply unsigned_lit_small. lia. }
assert (Hfwr : fw_writes (SF + 464) 8 = true)
  by (unfold fw_writes; destruct (Z.eqb_spec (SF + 464) 0) as [Hq|Hq]; [lia | reflexivity]).
assert (Hfwn : fw_n fw = n2 + 1) by (unfold fw_n; unfold n2, n1 in *; lia).
assert (Hzf3 : zero_shadow (aview SEGS (w_H W4) (ms_mem ms)) SHADOW_OFF (SF + 464) 8).
{ apply (h_zs_moved (aview SEGS (w_H W4) mem4)); [|exact Hzf2].
  intros i Hi. change (shadow_of_addr SHADOW_OFF (SF + 464)) with (shadow_addr (SF + 464)). rewrite Hshf58.
  apply KR2; unfold n2, n1 in *; clear - Hi Hsh1 C1 Hmf0 HSF0 HSF1 HshSF Hn1r; lia. }
(* ---- 0x81844: the call of reac_identity_fw_str ---- *)
eapply SRr_bind.
{ apply (HFWS LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly4 S4 W4 (ms_mem ms) _ K
    (ms_regs ms) fw (SF + 464) 8 HJ4).
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Q10, (EE2 21%nat 21%bv eq_refl), (P4 21%bv ltac:(cbn; tauto)). exact R21.
  - rewrite Q11, U2_20. unfold w64. f_equal. lia.
  - rewrite Q12. reflexivity.
  - exact Hfw.
  - lia. - lia.
  - rewrite Usp2. clear - Hmf32. lia.
  - rewrite Usp2. unfold REAC_IDENTITY_FW_STR_STK, FW_FRAME, ESTACK. clear - Hmfb HSTK' Has. lia.
  - rewrite Usp2. clear - Hmfb. lia.
  - intros _. unfold fw_dest_ok. rewrite Hfwn. split; [|split].
    + intros a Ha. right. exists 4, pos. split; [rewrite Hfrs4; left; reflexivity|].
      unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFa4, HFB. unfold n2, n1 in *. lia.
    + rewrite Usp2. eapply h_twr_frame; [exact HJ4 | | | ]; rewrite ?EFa4;
        unfold n2, n1 in *; clear - Hn1r HSF1 HSF0 Hmf0 Hes; lia.
    + apply (range_addressable_sub _ _ (SF + 464) 8);
        [ apply (zero_shadow_range _ _ (SF + 464) 8); [clear - HSF64; lia | reflexivity | exact Hzf3]
        | lia | unfold n2, n1 in *; lia ]. }
cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Hfrs5 & Hperm5 & Hpost5).
rewrite Hfwr in Hpost5. destruct Hpost5 as (R10_5 & HG5 & HK5).
rewrite Q1. rewrite Hfwn in HK5.
(* ---- back at 0x81848 ---- *)
rewrite Hfrs4 in Hfrs5.
assert (P5 : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr regs5 r = getr (ms_regs ms) r) by (h_pres0 HP5).
assert (KQ5 : forall a, 0 <= a < 2 ^ 64 -> CL a -> ~ (mf - 8192 <= a < mf \/ SF + 464 <= a < SF + 472) ->
  aview SEGS (w_H W5) mem5 a = aview SEGS (w_H W4) (ms_mem ms) a).
{ intros a Ha Hc Hw.
  apply (h_keep_tcj REAC_IDENTITY_FW_STR_STK ly4 S4 W4 (ms_mem ms) W5 mem5 (spZ (ms_regs ms)) _
    (ablocks B ly2 S2) pos SF (fun x => mf - 8192 <= x < mf \/ SF + 464 <= x < SF + 472)
    HK5 Hfrs4 EFa4 ltac:(intros b n Hb; rewrite Hbl4, Hbl3; exact Hb)
    ltac:(intros x Hx; rewrite Usp2 in Hx; unfold REAC_IDENTITY_FW_STR_STK, FW_FRAME, ESTACK in Hx; left; lia)
    ltac:(intros x Hx; cbn beta in Hx; right; unfold n2, n1 in *; lia));
  [exact Ha | exact Hc | exact Hw]. }
assert (Hz5 : zero_shadow (aview SEGS (w_H W5) mem5) SHADOW_OFF (SF + 496) 16).
{ apply (h_zs_moved (aview SEGS (w_H W4) (ms_mem ms))).
  - intros i Hi. change (shadow_of_addr SHADOW_OFF (SF + 496)) with (shadow_addr (SF + 496)). rewrite Hshef.
    apply KQ5; [clear - Hi Hsh1 C1; lia | right; right; left; lia | clear - Hi Hsh1 HshSF Hmf0 HSF0 HSF1 C1; lia].
  - apply (h_zs_moved (aview SEGS (w_H W4) mem4)); [|exact Hz2].
    intros i Hi. change (shadow_of_addr SHADOW_OFF (SF + 496)) with (shadow_addr (SF + 496)). rewrite Hshef.
    apply KR2; unfold n2, n1 in *; clear - Hi Hsh1 C1 Hmf0 HSF0 HSF1 HshSF Hn1r; lia. }
assert (Hzf5 : zero_shadow (aview SEGS (w_H W5) mem5) SHADOW_OFF (SF + 464) 8).
{ apply (h_zs_moved (aview SEGS (w_H W4) (ms_mem ms))); [|exact Hzf3].
  intros i Hi. change (shadow_of_addr SHADOW_OFF (SF + 464)) with (shadow_addr (SF + 464)). rewrite Hshf58.
  apply KQ5; [clear - Hi Hsh1 C1; lia | right; right; left; clear - Hi Hsh1; lia
  | clear - Hi Hsh1 HshSF Hmf0 HSF0 HSF1 C1; lia]. }
(* the bytes of ef, assembled at the memory of the fw_str call and moved to mem5 *)
assert (EFms : garr8 SEGS (rd W4 (ms_mem ms)) (SF + 496)
  (map bv_unsigned (IdentSpec.DEC v1 1) ++ [46] ++ map bv_unsigned (IdentSpec.DEC v2 3) ++ [0])).
{ apply h_garr8_app.
  - apply (h_garr8_moved (w_H W4) (w_H W4) mem4 (ms_mem ms)); [|exact HD3_4].
    intros j Hj. rewrite length_map, Hlen1 in Hj. apply KR2; unfold n2, n1 in *; lia.
  - rewrite length_map, Hlen1'. rewrite Z2Nat.id by (unfold n1 in *; lia).
    apply h_garr8_app.
    + intros j Hj. cbn [length] in Hj. assert (j = 0%nat) by lia. subst j. cbn [nth]. rewrite Z.add_0_r.
      split; [apply h_vm1; rewrite KR2 by (unfold n2, n1 in *; lia); exact VD1_4 | lia].
    + cbn [length]. replace (SF + 496 + n1 + Z.of_nat 1) with (SF + 496 + (n1 + 1)) by lia.
      apply h_garr8_app.
      * apply (h_garr8_moved (w_H W4) (w_H W4) mem4 (ms_mem ms)); [|exact HD4].
        intros j Hj. rewrite length_map, Hn2' in Hj. apply KR2; unfold n2, n1 in *; lia.
      * rewrite length_map, Hn2'. intros j Hj. cbn [length] in Hj. assert (j = 0%nat) by lia. subst j.
        cbn [nth]. rewrite Z.add_0_r. split; [apply h_vm1 | lia].
        replace (SF + 496 + (n1 + 1) + Z.of_nat 3) with (SF + 496 + n2) by (unfold n2; lia). exact VD2. }
assert (EF5 : garr8 SEGS (rd W5 mem5) (SF + 496)
  (map bv_unsigned (IdentSpec.DEC v1 1) ++ [46] ++ map bv_unsigned (IdentSpec.DEC v2 3) ++ [0])).
{ apply (h_garr8_moved (w_H W4) (w_H W5) (ms_mem ms) mem5); [|exact EFms].
  intros j Hj. rewrite !length_app, !length_map, Hlen1', Hn2'' in Hj. cbn [length] in Hj.
  apply KQ5; [unfold n2, n1 in *; lia | right; left; unfold n2, n1 in *; lia
  | unfold n2, n1 in *; clear - Hj Hmf0 HSF0 HSF1 Hn1r; lia]. }
assert (KQ5' : forall a, 0 <= a < 2 ^ 64 -> CL a -> ~ WR0 a -> aview SEGS (w_H W5) mem5 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hc Hw. rewrite KQ5; [| exact Ha | exact Hc | unfold WR0 in Hw; lia].
  rewrite KR2 by (unfold WR0 in Hw; unfold n2, n1 in *; lia). exact (KQ2 a Ha Hc Hw). }
clear EFms KR2 KQ5 Q1 Q10 Q11 Q12 HK5 Usp2 HJ4 VD2 HD4 HD3_4 VD1_4 Hz2 Hzf2 Hzf3 KQ2 HS.
(* ---- run 3: 0x81848 .. the bcmp call at 0x8185c ---- *)
remember (Eimg (Ereg regs5 (@nil word))) as E3 eqn:HE3.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply Eimg_env).
assert (EE3 : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E3 k = getr regs5 r)
  by (intros k r Hkr; rewrite HE3; apply ew_Eimg_Ereg_nat; exact Hkr).
assert (ER3 : regs_ok E3 sr_atoms regs5) by (rewrite HE3; apply regs_ok_Eimg_Ereg).
assert (AGE3 : env_agree 32 (Ereg regs5 (@nil word)) E3)
  by (rewrite HE3; split; [intros k Hkr; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE3.
assert (E3_10 : ew E3 10 = Z_to_bv 64 n2)
  by (rewrite (EE3 10%nat 10%bv eq_refl), R10_5, Hn1; unfold w64; f_equal; unfold n2; lia).
assert (E3_22 : ew E3 22 = Z_to_bv 64 n2)
  by (rewrite (EE3 22%nat 22%bv eq_refl), (P5 22%bv ltac:(cbn; tauto)), Q22; exact E2x35).
assert (E3_18 : ew E3 18 = Z_to_bv 64 (SF + 464)).
{ rewrite (EE3 18%nat 18%bv eq_refl), (P5 18%bv ltac:(cbn; tauto)), Q18, U2_20. f_equal. lia. }
assert (E3_20 : ew E3 20 = Z_to_bv 64 (SF + 496)).
{ rewrite (EE3 20%nat 20%bv eq_refl), (P5 20%bv ltac:(cbn; tauto)), (HKR2 20%bv ltac:(cbn; tauto)),
    (P4 20%bv ltac:(cbn; tauto)). exact R20. }
assert (R23_5 : getr regs5 23 = w64 (SlotModel.t_fam_raw inp)).
{ rewrite (P5 23%bv ltac:(cbn; tauto)), (HKR2 23%bv ltac:(cbn; tauto)), (P4 23%bv ltac:(cbn; tauto)). exact R23. }
assert (R24_5 : getr regs5 24 = w64 (SlotModel.t_cap_tok inp)).
{ rewrite (P5 24%bv ltac:(cbn; tauto)), (HKR2 24%bv ltac:(cbn; tauto)), (P4 24%bv ltac:(cbn; tauto)). exact R24. }
assert (R26_5 : getr regs5 26 = w64 (SlotModel.t_cap_name inp)).
{ rewrite (P5 26%bv ltac:(cbn; tauto)), (HKR2 26%bv ltac:(cbn; tauto)), (P4 26%bv ltac:(cbn; tauto)). exact R26. }
assert (R27_5 : getr regs5 27 = Z_to_bv 64 cd)
  by (rewrite (P5 27%bv ltac:(cbn; tauto)), Q27; exact E2x34).
assert (R2_5 : getr regs5 2 = w64 mf)
  by (rewrite (P5 2%bv ltac:(cbn; tauto)), (HKR2 2%bv ltac:(cbn; tauto)), (P4 2%bv ltac:(cbn; tauto)); exact Rsp).
assert (R9_5 : getr regs5 9 = w64 mf)
  by (rewrite (P5 9%bv ltac:(cbn; tauto)), (HKR2 9%bv ltac:(cbn; tauto)), (P4 9%bv ltac:(cbn; tauto)); exact Rs1).
assert (R8_5 : getr regs5 8 = w64 (e_sp0 g))
  by (rewrite (P5 8%bv ltac:(cbn; tauto)), (HKR2 8%bv ltac:(cbn; tauto)), (P4 8%bv ltac:(cbn; tauto)); exact Rs0).
assert (R3_5 : getr regs5 3 = w64 (as_gp B))
  by (rewrite (P5 3%bv ltac:(cbn; tauto)), (HKR2 3%bv ltac:(cbn; tauto)), (P4 3%bv ltac:(cbn; tauto)); exact Rgp).
assert (R4_5 : getr regs5 4 = w64 (as_tp B))
  by (rewrite (P5 4%bv ltac:(cbn; tauto)), (HKR2 4%bv ltac:(cbn; tauto)), (P4 4%bv ltac:(cbn; tauto)); exact Rtp).
assert (R19_5 : getr regs5 19 = w64 sh)
  by (rewrite (P5 19%bv ltac:(cbn; tauto)), (HKR2 19%bv ltac:(cbn; tauto)), (P4 19%bv ltac:(cbn; tauto)); exact Rs3).
clear P5 Q22 Q18 Q27 HKR2 HP5 ms.
assert (HS : st_ok_pi SEGS VAL E3 ss_h3
  (restrict (w_H W5) (mkst regs5 (Z_to_bv 64 (BASE + 0x113c)) mem5 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_h3. apply pa_entry_st_ok_full;
  [exact ER3 | vm_compute; reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
(* 0x81848 bltz a0: a0 = L fw = n2 >= 5 *)
psrr_branch_pi RUNP BR HS.
{ rewrite (h_blt E3 10%nat n2 E3_10 ltac:(unfold n2, n1 in *; lia)) in Hc.
  apply Z.ltb_lt in Hc. unfold n2, n1 in *. lia. }
clear Hc.
paj_run_sh RUNP HS HJ5.
{ apply awr_ok_nil. }
cbn [ms_mem mkst] in HF, HFr, HG.
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W5) (ms_mem ms) a = aview SEGS (w_H W5) mem5 a).
{ intros a Ha. apply (kept_of_frame E3 _ (w_H W5) mem5 (ms_mem ms) (fun _ => False) HFr); [|exact Ha|intros []].
  intros bb wlo whi aa Hin _. cbn in Hin. destruct Hin. }
clear HF HFr HG.
(* 0x8184c bne s6,a0: both are n2 *)
psrr_branch_pi RUNP BR HS.
{ rewrite branch_ne_U, (U_atom E3 22%nat n2 E3_22 ltac:(unfold n2, n1 in *; lia)),
    (U_atom E3 10%nat n2 E3_10 ltac:(unfold n2, n1 in *; lia)) in Hc.
  rewrite Z.eqb_refl in Hc. discriminate Hc. }
clear Hc.
paj_run_shc RUNP RUNC HS HJ5.
{ apply awr_ok_nil. }
cbn [ms_mem mkst] in HF, HFr, HG.
assert (K3b : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W5) (ms_mem ms0) a = aview SEGS (w_H W5) mem5 a).
{ intros a Ha. rewrite <- (K3 a Ha).
  apply (kept_of_frame E3 _ (w_H W5) (ms_mem ms) (ms_mem ms0) (fun _ => False) HFr); [|exact Ha|intros []].
  intros bb wlo whi aa Hin _. cbn in Hin. destruct Hin. }
clear HF HFr HG.
(* ---- 0x8185c: the call of bcmp ---- *)
pose proof HJ5 as (HAR5 & Hly5 & _ & _ & _ & _ & Hnev5 & _ & _ & _ & _ & _ & _ & Hpres5 & _).
pose proof Hly5 as (_ & _ & _ & _ & _ & EF5' & _).
assert (EFa5 : frame_addr ly5 4 pos = SF) by (change SF with (SFa g pos); unfold SFa, frame_addr; rewrite EF5'; reflexivity).
assert (Hin5 : In (4, pos) (frames S5)) by (rewrite Hfrs5; left; reflexivity).
destruct (al_frames _ _ LAWS ly5 S5 W5 (ms_mem ms0) _ 4 pos HAR5 Hin5) as (_ & HSFapp5 & HFpres & _).
rewrite EFa5, HFB in HSFapp5, HFpres.
destruct (frames_bounds SEGS B LAWS ly5 S5 W5 (ms_mem ms0) _ 4 pos HAR5 Hin5) as (HSF0' & HSF1' & _).
rewrite EFa5 in HSF0', HSF1'. rewrite HFB in HSF1'.
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
pose proof (regs_kept_of_st_ok SEGS E3 _ (restrict (w_H W5) ms0) regs5 _
  [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS AGE3 ltac:(vm_compute; reflexivity)) as HKR3.
cbn [ms_regs restrict] in HKR3.
pmkst HS.
assert (Usp3 : spZ (ms_regs ms0) = mf).
{ unfold spZ. rewrite (HKR3 2%bv ltac:(cbn; tauto)), R2_5. unfold w64. apply unsigned_lit_small. lia. }
assert (Hzf6 : zero_shadow (aview SEGS (w_H W5) (ms_mem ms0)) SHADOW_OFF (SF + 464) 8).
{ apply (h_zs_moved (aview SEGS (w_H W5) mem5)); [|exact Hzf5].
  intros i Hi. change (shadow_of_addr SHADOW_OFF (SF + 464)) with (shadow_addr (SF + 464)). rewrite Hshf58.
  apply K3b. clear - Hi Hsh1 C1. lia. }
assert (Hz6 : zero_shadow (aview SEGS (w_H W5) (ms_mem ms0)) SHADOW_OFF (SF + 496) 16).
{ apply (h_zs_moved (aview SEGS (w_H W5) mem5)); [|exact Hz5].
  intros i Hi. change (shadow_of_addr SHADOW_OFF (SF + 496)) with (shadow_addr (SF + 496)). rewrite Hshef.
  apply K3b. clear - Hi Hsh1 C1. lia. }
eapply SRr_bind.
{ eapply (aj_bcmp_at SEGS B LAWS pa_segs_low (SIGMA IS___interceptor_trampoline_bcmp) ABCMP
    W5 (ms_regs ms0) (ms_mem ms0) LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly5 S5 _ K (SF + 464) (SF + 496) (n2 + 1) (mf - sp0) _ HJ5).
  - rewrite Q10, E3_18. reflexivity.
  - rewrite Q11, E3_20. reflexivity.
  - rewrite Q12, E3_22, unsigned_lit_small by (unfold n2, n1 in *; lia). reflexivity.
  - unfold n2, n1 in *. lia.
  - lia. - unfold n2, n1 in *. lia. - lia. - unfold n2, n1 in *. lia.
  - rewrite Usp3. lia.
  - clear - Hmf32 Hsp0al. lia.
  - clear - Hmfb. lia.
  - unfold ESTACK. clear - Hmfb HSTK' Has. lia.
  - rewrite (HKR3 3%bv ltac:(cbn; tauto)). exact R3_5.
  - rewrite (HKR3 4%bv ltac:(cbn; tauto)). exact R4_5.
  - reflexivity.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [apply (aview_some_of_apresent SEGS); apply HFpres; unfold n2, n1 in *; lia|].
    rewrite Usp3. unfold ESTACK. clear - Ha HSF1' Hmf0 Hn1r; unfold n2, n1 in *; lia.
  - intros a Ha. split; [apply (aview_some_of_apresent SEGS); apply HFpres; unfold n2, n1 in *; lia|].
    rewrite Usp3. unfold ESTACK. clear - Ha HSF1' Hmf0 Hn1r; unfold n2, n1 in *; lia.
  - intros a Ha. unfold ESTACK. clear - Ha HSF1' Hmf0 Hn1r; unfold n2, n1 in *; lia.
  - intros a Ha. unfold ESTACK. clear - Ha HSF1' Hmf0 Hn1r; unfold n2, n1 in *; lia.
  - apply (amem_range_sub_app SF 1024); [exact HSFapp5 | lia | lia | unfold n2, n1 in *; lia | unfold n2, n1 in *; lia].
  - apply (amem_range_sub_app SF 1024); [exact HSFapp5 | lia | lia | unfold n2, n1 in *; lia | unfold n2, n1 in *; lia].
  - apply (range_addressable_sub _ _ (SF + 464) 8);
      [ apply (zero_shadow_range _ _ (SF + 464) 8); [clear - HSF64; lia | reflexivity | exact Hzf6]
      | lia | unfold n2, n1 in *; lia ].
  - intros _. eapply (shadow_hull_vis_of_frame SEGS B LAWS ly5 S5 W5 (ms_mem ms0) _ 4 pos _ _ HAR5 Hin5);
      [rewrite EFa5; lia | rewrite EFa5, HFB; unfold n2, n1 in *; lia | unfold n2, n1 in *; lia].
  - apply (range_addressable_sub _ _ (SF + 496) 16);
      [ apply (zero_shadow_range _ _ (SF + 496) 16); [clear - HSF64; lia | reflexivity | exact Hz6]
      | lia | unfold n2, n1 in *; lia ].
  - intros _. eapply (shadow_hull_vis_of_frame SEGS B LAWS ly5 S5 W5 (ms_mem ms0) _ 4 pos _ _ HAR5 Hin5);
      [rewrite EFa5; lia | rewrite EFa5, HFB; unfold n2, n1 in *; lia | unfold n2, n1 in *; lia]. }
cbv beta. intros W6 c6 Hwle6 (-> & regs6 & mem6 & md6 & v & -> & HJ6 & HP6 & R10_6 & Hcmp & HK6 & Hpres6).
rewrite Q1.
(* the formatter's output equals the expected string, NUL included: bcmp returned 0 *)
set (LEF := map bv_unsigned (IdentSpec.DEC v1 1) ++ [46] ++ map bv_unsigned (IdentSpec.DEC v2 3) ++ [0]) in *.
assert (HEFL : fw_bytes fw = LEF).
{ unfold fw_bytes, LEF. rewrite (reac_identity_fw_str_c.reac_identity_fw_str_c3 fw Hfw). rewrite !map_app.
  cbn [map]. rewrite <- !app_assoc. reflexivity. }
assert (HLEF : length LEF = Z.to_nat (n2 + 1)).
{ unfold LEF. rewrite !length_app, !length_map, Hlen1', Hn2'. cbn [length]. unfold n2, n1 in *. lia. }
assert (Hv0 : v = w64 0).
{ apply Hcmp. intros i Hi. rewrite !K3b by (unfold n2, n1 in *; lia).
  rewrite HEFL in HG5.
  replace i with (Z.of_nat (Z.to_nat i)) by lia.
  rewrite (h_garr8_aview _ _ _ _ _ HG5), (h_garr8_aview _ _ _ _ _ EF5); [reflexivity | |];
  rewrite HLEF; lia. }
clear Hcmp Q10 Q11 Q12 HS.
(* ---- run 4: 0x81860 .. 0x81878: bnez a0, a1 = s7 << 56, the shadow of f and ef poisoned again ---- *)
assert (P6 : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr regs6 r = getr regs5 r).
{ intros r Hr. rewrite <- (HKR3 r Hr). revert r Hr. h_pres0 HP6. }
pose proof HJ6 as (HAR6 & _).
destruct (al_frames _ _ LAWS ly5 S5 W5 mem6 _ 4 pos HAR6 Hin5) as (_ & _ & _ & HFS6).
rewrite EFa5, HFB in HFS6. fold sh in HFS6.
remember (Eimg (Ereg regs6 (@nil word))) as E4 eqn:HE4.
assert (HEI4 : img_env VAL A_LIM E4) by (rewrite HE4; apply Eimg_env).
assert (EE4 : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E4 k = getr regs6 r)
  by (intros k r Hkr; rewrite HE4; apply ew_Eimg_Ereg_nat; exact Hkr).
assert (ER4 : regs_ok E4 sr_atoms regs6) by (rewrite HE4; apply regs_ok_Eimg_Ereg).
assert (AGE4 : env_agree 32 (Ereg regs6 (@nil word)) E4)
  by (rewrite HE4; split; [intros k Hkr; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE4.
assert (U4_19 : bv_unsigned (ew E4 19) = sh).
{ rewrite (EE4 19%nat 19%bv eq_refl), (P6 19%bv ltac:(cbn; tauto)), R19_5. unfold w64. apply unsigned_lit_small.
  clear - Hsh1 C1. lia. }
assert (E4_10 : ew E4 10 = Z_to_bv 64 0) by (rewrite (EE4 10%nat 10%bv eq_refl), R10_6, Hv0; reflexivity).
assert (Hfam : 0 <= SlotModel.t_fam_raw inp < 256) by (unfold SlotModel.t_fam_raw, SlotModel.tb; apply SlotModel.inb_range).
assert (E4_23 : ew E4 23 = Z_to_bv 64 (SlotModel.t_fam_raw inp))
  by (rewrite (EE4 23%nat 23%bv eq_refl), (P6 23%bv ltac:(cbn; tauto)), R23_5; reflexivity).
pose proof (h_sll56 E4 _ E4_23 Hfam) as Hsll. unfold h_SLL56 in Hsll.
assert (HS : st_ok_pi SEGS VAL E4 ss_h4
  (restrict (w_H W5) (mkst regs6 (Z_to_bv 64 (BASE + 0x1154)) mem6 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_h4. apply pa_entry_st_ok_full.
  - exact ER4.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold h_s3, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U4_19.
    split; [clear - Hsh1; lia|]. split; [clear - Hsh1 C1; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply (HFS6 o). change (1024 / 8) with 128. lia.
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - split; [exact I | split; exact I]. }
(* 0x81860 bnez a0: bcmp returned 0 *)
psrr_branch_pi RUNP BR HS.
{ rewrite branch_ne_U, (U_atom E4 10%nat 0 E4_10 ltac:(lia)), U_lit in Hc by lia. discriminate Hc. }
clear Hc.
paj_run_sh RUNP HS HJ6.
{ intros a (r & Hr & Ha). cbn [ss_mem add_cond ss_h4 In] in Hr. destruct Hr as [<- | []].
  unfold h_s3 in Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U4_19 in Ha.
  right; right; right. exists 4, pos. split; [left; reflexivity|]. right. unfold in_zr; cbn [fst snd].
  rewrite EFa5, HFB. fold sh. change (1024 / 8) with 128. lia. }
cbn [ms_mem mkst] in HF, HFr, HG.
assert (K4 : forall a, 0 <= a < 2 ^ 64 -> ~ (sh + 58 <= a < sh + 64) ->
  aview SEGS (w_H W5) (ms_mem ms1) a = aview SEGS (w_H W5) mem6 a).
{ intros a Ha Hw.
  apply (kept_of_frame E4 _ (w_H W5) mem6 (ms_mem ms1) (fun x => sh + 58 <= x < sh + 64) HFr); [|exact Ha|exact Hw].
  intros bb wlo whi aa Hin Hr. unfold windows in Hin. cbn in Hin.
  destruct Hin as [Eq | []]; injection Eq as <- <- <-; cbn [base_val] in Hr. rewrite U4_19 in Hr. lia. }
clear HF HFr HG.
prreg_raw HS (11%bv : bv 5) Q11. rewrite Hsll in Q11.
pose proof (regs_kept_of_st_ok SEGS E4 _ (restrict (w_H W5) ms1) regs6 _
  [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS AGE4 ltac:(vm_compute; reflexivity)) as HKR4.
cbn [ms_regs restrict] in HKR4.
assert (RF : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms1) r = getr regs5 r) by (intros r Hr; rewrite (HKR4 r Hr); exact (P6 r Hr)).
(* ---- the boundary inv_H_end at 0x81878 ---- *)
assert (KF : forall a, 0 <= a < 2 ^ 64 -> CL a -> ~ WR0 a -> ~ (sh + 58 <= a < sh + 64) ->
  aview SEGS (w_H W5) (ms_mem ms1) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hc Hw Hw'. rewrite (K4 a Ha Hw').
  rewrite HK6 by (unfold WR0 in Hw; lia). rewrite (K3b a Ha). exact (KQ5' a Ha Hc Hw). }
assert (VMS : forall a (n : nat) vv, mf <= a -> a + Z.of_nat n <= sp0 -> (a + Z.of_nat n <= mf + 208 \/ mf + 216 <= a) ->
  val_mem SEGS (rd W2 mem2) a n vv -> val_mem SEGS (rd W5 (ms_mem ms1)) a n vv).
{ intros a n vv H1 H2 H3 Hv. apply (val_mem_moved SEGS (w_H W2) (w_H W5) mem2 (ms_mem ms1) a a n vv); [|exact Hv].
  intros kk Hkk. apply KF; [clear - H1 H2 Hkk Hmfb Hmf0 Hshi H47 C1; lia | left; clear - H1 Hkk Hmf0; lia
  | unfold WR0; clear - H1 H2 H3 Hkk Hmf0 HSF1 C1; lia | clear - H1 Hkk Hmf0 Hsh1; lia]. }
assert (FK : forall a, SF <= a < SF + 1024 -> ~ (SF + 464 <= a < SF + 512) ->
  aview SEGS (w_H W5) (ms_mem ms1) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hw. apply KF; [clear - Ha HSF0 HSF1 C1; lia | right; left; exact Ha
  | unfold WR0; clear - Ha Hw HSF1 Hmf0 C1; lia | clear - Ha HshSF; lia]. }
assert (SHK : forall a, sh <= a < sh + 58 -> aview SEGS (w_H W5) (ms_mem ms1) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. apply KF; [clear - Ha Hsh1 C1; lia | right; right; left; lia | apply HshWR; lia | lia]. }
apply SRr_ret.
unfold inv_H_end, acut. pmkst HS.
exists ly5, S5, (ms_regs ms1), (ms_mem ms1). eexists.
split; [unfold cfg_at; reflexivity|].
split; [exact HJ6|].
split; [exact Hfrs5|].
split; [exact Hk|].
split; [eapply (mo_le_mono MT MTL); [exact (mo_le_trans MT MTL _ _ _ _ _ MLE (HMT0 S2 S5)) | lia]|].
split; [apply (mo_ok_step MT MTL S2 S5 0); [rewrite Z.add_0_l; exact MOK | exact (HMT0 S2 S5)]|].
(* the input block: kept (no step writes a heap block) *)
assert (HINB : bytes_at8 W5 (ms_mem ms1) (e_p g) inp).
{ unfold bytes_at8 in *. apply (h_garr8_moved (w_H W2) (w_H W5) mem2 (ms_mem ms1)); [|exact Hinb].
  intros j Hj. rewrite length_map in Hj. rewrite <- Hlen in Hj.
  destruct Hinp as [[Hn0 _] | [[Hn0 Hn26] Hine]]; [clear - Hj Hn0; lia|].
  assert (Hine2 : In (e_p g, e_n g) (ablocks B ly2 S2)).
  { destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). exact Hine. }
  destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 (e_p g) (e_n g) HAR2 Hine2) as (_ & Hp4096 & Hpce & Hpapp & _).
  pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 (e_p g) (e_n g) 4 pos HAR2 Hine2 Hin4) as Hdf.
  unfold zdisjoint in Hdf. cbn [fst snd] in Hdf. rewrite EFa, HFB in Hdf.
  pose proof (req_size_pos (e_n g) ltac:(lia)) as Hrq.
  apply KF.
  - clear - Hj Hpce Hp4096 Hrq C1. lia.
  - right; right; right. exists (e_p g), (e_n g), j. split; [exact Hine2|]. split; [clear - Hj Hrq; lia | reflexivity].
  - unfold WR0. clear - Hj Hpce Hp4096 Hrq Hdf Hmf0 C1. lia.
  - intros Hw. apply (fshadow_not_app SF 128 (e_p g) (req_size (e_n g)) (e_p g + j));
      [exact HSF0 | clear - HSF1 C1; lia | exact Hpapp | | clear - Hj Hrq; lia].
    rewrite Esh in Hw. unfold SHADOW_OFF in Hw. clear - Hw. lia. }
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ6) as [Efd Efs].
assert (VF : val_mem SEGS (rd W5 (ms_mem ms1)) (SF + 1016) 8 (flag_addr (e_ly g) 4 pos)).
{ apply (val_mem_moved SEGS (w_H W2) (w_H W5) mem2 (ms_mem ms1) (SF + 1016) (SF + 1016) 8); [|exact Vflag].
  intros kk Hkk. apply FK; change (Z.of_nat 8) with 8 in Hkk; lia. }
split.
{ unfold ecommon. change (e_sp0 g) with sp0. change (SFa g pos) with SF.
  split; [rewrite (RF 2%bv ltac:(cbn; tauto)); exact R2_5|].
  split; [rewrite (RF 9%bv ltac:(cbn; tauto)); exact R9_5|].
  split; [rewrite (RF 8%bv ltac:(cbn; tauto)); exact R8_5|].
  split; [exact Hmfb|]. split; [exact Hmf32|].
  split; [rewrite (RF 3%bv ltac:(cbn; tauto)); exact R3_5|].
  split; [rewrite (RF 4%bv ltac:(cbn; tauto)); exact R4_5|].
  split; [rewrite (RF 19%bv ltac:(cbn; tauto)); exact R19_5|].
  repeat match goal with
    | |- _ /\ _ => split
    | |- e_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact HPRE
    | |- forall fd, _ => intros fd; rewrite Efd; reflexivity
    | |- m_fs _ = _ => exact Efs
    | |- bytes_at8 _ _ (e_p g) _ => exact HINB
    | |- val_mem _ _ (SF + 1016) _ _ => exact VF
    | |- val_mem _ _ ?a _ _ => apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | clear - Hmfb; lia | assumption]
    end. }
unfold id_at, hblocks, mf_id3, mf_id. change (SFa g pos) with SF.
assert (HEFL2 : LEF = map bv_unsigned (SlotModel.t_EF inp) ++ [0]).
{ unfold LEF, SlotModel.t_EF. rewrite !map_app. cbn [map]. rewrite <- !app_assoc. reflexivity. }
assert (Lid : Z.of_nat (length (map (fun b : byte => bv_unsigned b) (m_id g (m_nrec g)))) = 38).
{ rewrite length_map. unfold m_id. rewrite SlotModel.rec_id_length. reflexivity. }
split; [split; [|split]|].
- unfold bytes_at8 in *. apply (h_garr8_moved (w_H W2) (w_H W5) mem2 (ms_mem ms1)); [|exact Hidb].
  intros kk Hkk. rewrite Lid in Hkk. apply FK; unfold V_id; clear - Hkk HSF0; lia.
- unfold sh_zero in *. apply (h_zs_moved (aview SEGS (w_H W2) mem2)); [|exact Hidz].
  intros i Hi. unfold V_id, N_id in *. unfold shadow_of_addr.
  replace (SHADOW_OFF + (SF + 352) / 8 + i) with (sh + 44 + i) by (rewrite Esh; clear - HSF64 Hi; unfold SHADOW_OFF; lia).
  apply SHK. clear - Hi. change (38 / 8) with 4 in Hi. lia.
- unfold sh_blk in *. apply (h_bs_moved (aview SEGS (w_H W2) mem2)); [|exact Hidk].
  intros i Hi. unfold V_id, N_id in *. unfold shadow_of_addr.
  replace (SHADOW_OFF + (SF + 352) / 8 + i) with (sh + 44 + i) by (rewrite Esh; clear - HSF64 Hi; unfold SHADOW_OFF; lia).
  apply SHK. clear - Hi. change ((38 + 7) / 8) with 5 in Hi. lia.
- split.
  { destruct Hbl as [Hperm Hf]. split; [|exact Hf]. eapply Permutation_trans; [exact Hperm5|].
    rewrite Hbl4, Hbl3. exact Hperm. }
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | clear - Hmfb; lia | exact Hid3]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | clear - Hmfb; lia | exact Hmid]|].
  split.
  { unfold bytes_at8, V_ef. apply (h_garr8_prefix _ _ _ [0]).
    assert (HEFL3 : map (fun b : byte => bv_unsigned b) (SlotModel.t_EF (e_pl g)) ++ [0] = LEF) by exact (eq_sym HEFL2).
    rewrite HEFL3.
    apply (h_garr8_moved (w_H W5) (w_H W5) mem5 (ms_mem ms1)); [|exact EF5].
    intros kk Hkk. rewrite HLEF in Hkk.
    rewrite K4 by (unfold n2, n1 in *; clear - Hkk HshSF HSF0 HSF1 C1 Hn1r; lia).
    rewrite HK6 by (unfold ESTACK; unfold n2, n1 in *; clear - Hkk HSF0 HSF1 Hmf0 C1 Hn1r Hmfb HSTK' Has; lia).
    apply K3b. unfold n2, n1 in *; clear - Hkk HSF0 HSF1 C1 Hn1r; lia. }
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | clear - Hmfb; lia | exact V136]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | clear - Hmfb; lia | exact V144]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | clear - Hmfb; lia | exact V160]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | clear - Hmfb; lia | exact V168]|].
  split; [exact Q11|].
  split; [rewrite (RF 23%bv ltac:(cbn; tauto)); exact R23_5|].
  split; [rewrite (RF 24%bv ltac:(cbn; tauto)); exact R24_5|].
  split; [rewrite (RF 26%bv ltac:(cbn; tauto)); exact R26_5|].
  rewrite (RF 27%bv ltac:(cbn; tauto)). exact R27_5.
Qed.

End c.
End b.
End a.
