(* fuzz_recv on image A: the step of its walk through a call of checked_memcpy / checked_memset (+0xd0, +0xf4,
   +0x120), on the invariant of lib/A/Prog/fuzz_recv_defs.v.
   - rv_preserved: the registers sp, gp, tp, s0, s1, s2, s3, s4, s9, s10, s11 a callee keeps (aregs_preserved);
   - rv_intrin: at a call whose destination [d, d + n) lies in the buffer, rv_inv holds at the return, the
     destination holds the copied bytes (or the fill byte), and every other byte outside the callee's window
     [sp - ESTACK, sp) (sp = entry sp - 96) is as at the call. The call's premises (link_ajkit.v aj_gx_intrin_at:
     the journal, the window, the destination bytes, the shadow of the destination) come from rv_inv and from the
     premises of fuzz_recv's own call (rv_call): a destination byte is a byte of the write set fuzz_recv_awr.
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk fuzz_recv_c fuzz_recv_defs fuzz_recv_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Variable c : rvc.
Hypothesis HC : rv_call SK B c.

(* the registers of the invariant and of the pieces' facts that a callee keeps *)
Lemma rv_preserved : forall regs regs2, aregs_preserved regs regs2 ->
  getr regs2 2 = getr regs 2 /\ getr regs2 3 = getr regs 3 /\ getr regs2 4 = getr regs 4 /\
  getr regs2 8 = getr regs 8 /\ getr regs2 9 = getr regs 9 /\ getr regs2 18 = getr regs 18 /\
  getr regs2 19 = getr regs 19 /\ getr regs2 20 = getr regs 20 /\ getr regs2 25 = getr regs 25 /\
  getr regs2 26 = getr regs 26 /\ getr regs2 27 = getr regs 27.
Proof.
  intros regs regs2 HP.
  assert (K : forall (rr : bv 5) z, rr = Z_to_bv 5 z -> acallee_saved z -> getr regs2 rr = getr regs rr).
  { intros rr z -> Hz. exact (HP z Hz). }
  split; [exact (K 2%bv 2 ltac:(apply bv_eq; reflexivity) ltac:(unfold acallee_saved; lia))|].
  split; [exact (K 3%bv 3 ltac:(apply bv_eq; reflexivity) ltac:(unfold acallee_saved; lia))|].
  split; [exact (K 4%bv 4 ltac:(apply bv_eq; reflexivity) ltac:(unfold acallee_saved; lia))|].
  split; [exact (K 8%bv 8 ltac:(apply bv_eq; reflexivity) ltac:(unfold acallee_saved; lia))|].
  split; [exact (K 9%bv 9 ltac:(apply bv_eq; reflexivity) ltac:(unfold acallee_saved; lia))|].
  split; [exact (K 18%bv 18 ltac:(apply bv_eq; reflexivity) ltac:(unfold acallee_saved; lia))|].
  split; [exact (K 19%bv 19 ltac:(apply bv_eq; reflexivity) ltac:(unfold acallee_saved; lia))|].
  split; [exact (K 20%bv 20 ltac:(apply bv_eq; reflexivity) ltac:(unfold acallee_saved; lia))|].
  split; [exact (K 25%bv 25 ltac:(apply bv_eq; reflexivity) ltac:(unfold acallee_saved; lia))|].
  split; [exact (K 26%bv 26 ltac:(apply bv_eq; reflexivity) ltac:(unfold acallee_saved; lia))|].
  exact (K 27%bv 27 ltac:(apply bv_eq; reflexivity) ltac:(unfold acallee_saved; lia)).
Qed.

(* THE CALL OF checked_memcpy / checked_memset into the buffer, on rv_inv *)
Lemma rv_intrin : forall op pc, aintrin_realizes SEGS B op pc ->
  forall regs mem md d x n raw,
  rv_inv SK B c regs mem md ->
  getr regs 10 = w64 d -> getr regs 11 = w64 x -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 ->
  rv_buf c <= d -> d + n <= rv_buf c + rv_len c ->
  getr regs 1 = raw -> YK0s.ret_ok raw ->
  (match op with
   | OCpy => 0 <= x /\ x + n <= 2 ^ 63 /\ src_ok SEGS (c_W c) regs mem x n /\ (d + n <= x \/ x + n <= d) /\
             amem_range x n /\ range_addressable (aview SEGS (w_H (c_W c)) mem) SHADOW_OFF x n /\
             (0 < n -> shadow_hull_vis (aview SEGS (w_H (c_W c)) mem) x n)
   | OSet => True end) ->
  SRr SEGS (c_W c) (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom SEGS)) md)
    (fun W2 c2 => W2 = c_W c /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
       rv_inv SK B c regs2 mem2 md2 /\ aregs_preserved regs regs2 /\
       (forall i, 0 <= i < n -> aview SEGS (w_H (c_W c)) mem2 (d + i) =
          match op with OCpy => aview SEGS (w_H (c_W c)) mem (x + i) | OSet => Some (x mod 256) end) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (rv_sp c - 96 - ESTACK <= a < rv_sp c - 96) ->
          aview SEGS (w_H (c_W c)) mem2 a = aview SEGS (w_H (c_W c)) mem a)).
Proof.
  intros op pc AI regs mem md d x n raw HI Ha0 Ha1 Ha2 Hn Hd1 Hd2 Hra Hraw Hsrc.
  pose proof HI as (HJ & Hfd & Hfs & Hsp & H3 & H4 & H26 & H27 & HFV & UN & PR).
  pose proof HC as ((_ & HGX & _ & _ & _ & Hgp & Htp & _ & _ & _ & _ & _ & Hajw & _) &
    _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Habuf & _ & Hrab & Hhb & _ & _).
  destruct (rv_sp_bounds SK B c HC) as (Hceil & Hlo & Hhi & H47 & Hsp16 & HXO).
  destruct (rv_pre_facts SK B TL c HC) as (Hb0 & Hlen & Hamr & Hbg & Hbf & Hef & Heg & He0 & He1).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  change (ard SEGS (rdW (c_W c) (c_memc c))) with (aview SEGS (w_H (c_W c)) (c_memc c)) in Hrab, Hhb.
  (* the call's sp is the frame base rv_sp - 96 *)
  assert (Usp : spZ regs = rv_sp c - 96).
  { unfold spZ. rewrite Hsp. apply unsigned_lit_small.
    clear - Hceil Hlo Hhi H47 HXO C1a. unfold FUZZ_RECV_AK, FUZZ_RECV_AFRAME, ESTACK in Hlo. lia. }
  assert (H16' : spZ regs mod 16 = 0) by (rewrite Usp; clear - Hsp16; lia).
  assert (Hlo' : c_sp0 c - c_STK c <= spZ regs - ESTACK)
    by (rewrite Usp; clear - Hlo; unfold FUZZ_RECV_AK, FUZZ_RECV_AFRAME, ESTACK in *; lia).
  assert (Hhi' : spZ regs <= c_sp0 c) by (rewrite Usp; clear - Hhi; lia).
  assert (Hgp' : getr regs 3 = w64 (as_gp B)) by (rewrite H3; exact Hgp).
  assert (Htp' : getr regs 4 = w64 (as_tp B)) by (rewrite H4; exact Htp).
  (* the destination range is a sub-range of the buffer *)
  assert (Hd0 : 0 <= d) by (clear - Hb0 Hd1; lia).
  assert (Hdk : d + n <= kHighMemEnd)
    by (clear - Hamr Hd1 Hd2 Hn C3 C4 C5; unfold amem_range in Hamr; lia).
  assert (Hdn : d + n <= 2 ^ 63) by (clear - Hdk C4; lia).
  assert (Hamd : amem_range d n) by (clear - Hamr Hd1 Hd2 Hn; unfold amem_range in *; lia).
  assert (Hra_d : range_addressable (aview SEGS (w_H (c_W c)) mem) SHADOW_OFF d n).
  { apply (rv_ra_kept SK B TL c HC regs mem md d n HI Hd0 Hdk).
    apply (range_addressable_sub _ _ (rv_buf c) (rv_len c)); [exact Hrab | lia | lia]. }
  assert (Hhull_d : 0 < n -> shadow_hull_vis (aview SEGS (w_H (c_W c)) mem) d n).
  { intros Hn0. apply (rv_hull_kept SK B TL c HC regs mem md d n HI Hd0 Hdk Hn0).
    apply (rv_hull_sub _ (rv_buf c) (rv_len c)); [exact Hhb | lia | lia | exact Hn0]. }
  eapply SRr_mono.
  { refine (aj_gx_intrin_at SK SEGS B LAWS pa_segs_low op pc AI (c_G c) (c_XO c) (c_OUT c) (c_W c) regs mem
      (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c) (c_mem0 c) (c_md0 c) (c_own c) (c_lyc c) (c_Sc c) md
      (c_k c) d x n raw HGX HJ Ha0 Ha1 Ha2 Hn Hd0 Hdn H16' Hlo' Hhi' Hgp' Htp' Hra Hraw _ Hamd Hra_d Hhull_d Hsrc).
    (* a destination byte is a byte of the buffer, a byte of fuzz_recv's write set *)
    intros a Ha.
    assert (Hab : rv_buf c <= a < rv_buf c + rv_len c) by (clear - Ha Hd1 Hd2; lia).
    assert (HW : inFP (fuzz_recv_awr (c_regs0 c) (rdW (c_W c) (c_memc c))) a).
    { exists (aarg (c_regs0 c) 1, aarg (c_regs0 c) 1 + aarg (c_regs0 c) 2).
      split; [unfold fuzz_recv_awr; cbn [In]; right; left; reflexivity | exact Hab]. }
    destruct (Hajw a HW) as [[Haw Hxo] | [HG | HO]].
    - left. split; [exact Haw|]. split; [exact Hxo|]. rewrite Usp.
      clear - Hbf Hab. unfold apart_frame, rv_buf, rv_len, rv_sp, FUZZ_RECV_AK, FUZZ_RECV_AFRAME, ESTACK in *. lia.
    - right; left. split; [exact HG|].
      apply (writable_kept (w_H (c_W c)) (c_memc c) mem a (PR a)).
      destruct Habuf as (junk & Hjl & _ & Hwr). unfold awrange in Hwr.
      replace a with (aarg (c_regs0 c) 1 + (a - aarg (c_regs0 c) 1)) by lia.
      apply Hwr. rewrite Hjl. unfold rv_buf, rv_len in Hab. lia.
    - right; right. exact HO. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & H10 & Hres & Hfr & Hpres2 & Hsm).
  rewrite Usp in Hfr.
  split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|].
  destruct (rv_preserved regs regs2 HP) as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E25 & E26 & E27).
  split.
  { apply (rv_inv_step SK B TL c HC regs mem md regs2 mem2 md2
      (fun a => (d <= a < d + n) \/ (rv_sp c - 96 - ESTACK <= a < rv_sp c - 96)) HI HJ2).
    - rewrite (same_but_materialized_wvb _ _ Hsm). exact (proj1 (wvb_fds_fs _ _ _)).
    - rewrite (same_but_materialized_wvb _ _ Hsm). exact (proj2 (wvb_fds_fs _ _ _)).
    - intros a Ha HZ. cbv beta in HZ.
      apply Hfr; [exact Ha | intros H; apply HZ; left; exact H | intros H; apply HZ; right; exact H].
    - intros a HZ. cbv beta in HZ. destruct HZ as [Ha | Ha].
      + right. unfold rv_ewr. right; right; left. clear - Ha Hd1 Hd2. lia.
      + left. clear - Ha. unfold FUZZ_RECV_AK, FUZZ_RECV_AFRAME, ESTACK in *. lia.
    - exact Hpres2.
    - exact E2.
    - exact E3.
    - exact E4.
    - exact E26.
    - exact E27. }
  split; [exact HP|]. split; [exact Hres|].
  intros a Ha Hd Hw. exact (Hfr a Ha Hd Hw).
Qed.
End w.
