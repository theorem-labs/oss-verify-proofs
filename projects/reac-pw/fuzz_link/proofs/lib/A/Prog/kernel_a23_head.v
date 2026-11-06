(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: off_img's image bounds cite this unit's own image (YImgTop.IMG_LO and YImgTop.IMG_TOP, which YImgTop.v of reac-pw/fuzz_rate gives as 0x10000 and 0x5fa000, both of this unit's ASan builds) in place of cgif's 0x10000 and 0x5fb000. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YCbq.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_rate. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/Reusable/YCbq.v, with its module paths and module names changed; 442 of its 486 lines of code are new or changed and 3116 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/kernel_k3.v, with its numbers changed; 136 of its 226 lines of code are new or changed and 396 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the walk of kernel's attribute cases a % 6 in {2, 3}: the nest's header and the nested
   attribute. Listing (internal path) (internal record, sha256 7bc02d6772b3), +0xaa0 .. +0xd64.
   (H) a23_head: kin_acase at +0xaa0 (KP_A23) -> J2 (+0xbf4). s10 := n0 = w2.n; two 2-byte puts, (0, 0) and
   (0x12, 0), each behind its room test. Groups (n at the cut; the taken room tests' offsets c of `n + c`):
     n <= 4092: both (pl 4) | 4093..4094: the first (pl 2) | 4095..4096: none.
   (M) a23_mid: J2 -> J6 (+0xdb8) when a1 <> 3 (`bne a1, 3`, a condition on the register's atom), else J2 -> J5
   (+0xd68): the nested attribute's length (8, 0), type (2, 0) and body "data". Groups:
     n <= 4088: all three (pl 8) | 4089..4092: the first two (pl 4) | 4093..4094: the first (pl 2) | 4095..4096: none.
   Each group is ONE run (kernel_a23_defs.v a23_ss, a23_seat); the cut after it by a23_landk (kernel_kit.v
   kat_frame_w2 and kw_move).
   Section hypotheses used: LAWS (the run instances).
   Released proofs (rule 24): none of kernel's walk (lookups/walk-lookups.md (internal record, sha256 98fff7967d93): disposition none, written new; confirmed by
   the rule-24 walk check at 14:56Z).
   Proves no function (kind: segment lemma of kernel's walk). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNlw LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
kernel_c kernel_defs kernel_kit kernel_next kernel_k3 kernel_a5 kernel_a23_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation BASE := (pa_val A_TEXT).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.

(* ---- THE END of a put run: the lane's cut at pc' ---- *)
Lemma a23_end : forall POST (Rc Rm Ra : kcx -> Z -> Prop) cx fpos k2 ly3 S3 W3 (ms3 : machine_state) md3
    c ci j m k n f adv hd kd left a p n0 pc rl (E : env) lo hi pl cs xc pc',
  kfrom SK B POST (a23_at B Rc Rm Ra pc') ->
  kbase SK B cx ->
  frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  Rc cx (c - ci) -> Rm cx (m - k) -> Ra cx left ->
  1 <= c <= 3 -> 0 <= ci < c -> 0 <= j <= ci -> 1 <= m <= 5 -> 0 <= k < m -> (kd = 0 \/ kd = 7) ->
  1 <= left <= 4 -> 0 <= hd <= n -> 0 <= a < 256 -> ktext cx p -> ka_text cx a p -> 0 <= n0 <= n ->
  kw_at W3 ms3 (kW2 cx fpos) n f ->
  kat B cx fpos pc rl (a23_sl cx fpos c ci m k hd kd) (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3 ->
  (forall rv, In rv [(19%nat, ka0 cx + 8); (21%nat, kW2 cx fpos); (24%nat, kS8 cx); (22%nat, left); (23%nat, a);
                     (27%nat, p)] -> In rv rl) ->
  bv_unsigned (ew E 21) = kW2 cx fpos -> bv_unsigned (ew E 32) = n -> bv_unsigned (ew E 33) = f ->
  bv_unsigned (ew E 34) = kW2 cx fpos + n ->
  0 <= pl -> n + pl <= 4096 ->
  forall (ms : machine_state) md cs' fe f',
  region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms)) (YP09.mkRegion (Some 21%nat) 4096 4112 4096 4112 cs') ->
  frame_of E (ss_mem (a23_ss pc lo hi pl cs xc)) (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) ->
  mem_grows (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms) md k2 ->
  kms pc' ms ->
  (forall r, In r nx_keep0 -> getr (ms_regs ms) r = getr (ms_regs ms3) r) ->
  (forall r : nat, In r [19; 21; 24; 22; 23; 27]%nat ->
     getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat r)) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat r))) ->
  getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat 25)) = sv_denot E (SOff 21 4096) ->
  getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat 26)) = w64 n0 ->
  m_fds md = m_fds md3 -> m_fs md = m_fs md3 ->
  In (YP09.mkChunk 4096 (CVal 8 (SOff 32 pl))) cs' ->
  In (YP09.mkChunk 4104 (CVal 4 fe)) cs' ->
  (fe = SOff 33 0 /\ f' = f) \/ (fe = SLit 1 /\ f' = 1) ->
  SRr SEGS W3 (mkCfg ms md) (POST cx).
Proof.
  intros POST Rc Rm Ra cx fpos k2 ly3 S3 W3 ms3 md3 c ci j m k n f adv hd kd left a p n0 pc rl E lo hi pl cs xc pc'
    HN HB HFR HRc HRm HRa Hc Hci Hj Hm Hk Hkd Hl Hhd Ha Htx Hka Hn0 HW HAT Hrl B21 B32 B33 B34 Hpl Hnpl
    ms md cs' fe f' HR1 HFr HG HJ HMS HK0 HK H25 H26 Hfds Hfs Hin1 Hin2 Hfe.
  pose proof HAT as (_ & HR0 & HRL & _).
  pose proof HW as (_ & _ & _ & _ & _ & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  assert (HR0' : kregs0 cx ms) by exact (kregs0_keep cx ms3 ms HK0 HR0).
  assert (HRL' : kregs_eq ms (a23_rl cx fpos a p n0 left)).
  { unfold kregs_eq, a23_rl. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    - rewrite (HK 19%nat) by kn_in. apply (kn_reg_of ms3 _ 19 _ HRL). apply Hrl. kn_in.
    - rewrite (HK 21%nat) by kn_in. apply (kn_reg_of ms3 _ 21 _ HRL). apply Hrl. kn_in.
    - rewrite (HK 24%nat) by kn_in. apply (kn_reg_of ms3 _ 24 _ HRL). apply Hrl. kn_in.
    - rewrite H25. cbn [sv_denot]. rewrite B21. reflexivity.
    - rewrite (HK 22%nat) by kn_in. apply (kn_reg_of ms3 _ 22 _ HRL). apply Hrl. kn_in.
    - rewrite (HK 23%nat) by kn_in. apply (kn_reg_of ms3 _ 23 _ HRL). apply Hrl. kn_in.
    - rewrite (HK 27%nat) by kn_in. apply (kn_reg_of ms3 _ 27 _ HRL). apply Hrl. kn_in.
    - exact H26. }
  destruct (a23_landk SK B LAWS cx fpos pc rl _ adv j k2 ly3 S3 W3 ms3 md3 n f E lo hi pl cs xc ms md cs' fe f'
              pc' _ HB HAT ltac:(reflexivity) HW B21 B32 B33 B34 Hpl Hnpl HR1 HFr HG HMS HR0' HRL' Hfds Hfs
              Hin1 Hin2 Hfe) as (HW' & HAT').
  apply (HN cx fpos k2 ly3 S3 W3 ms md HB HJ HFR).
  exists c, ci, j, m, k, (n + pl), f', adv, hd, kd, left, a, p, n0.
  split; [exact HRc|]. split; [exact HRm|]. split; [exact HRa|]. split; [exact Hc|]. split; [exact Hci|].
  split; [exact Hj|]. split; [exact Hm|]. split; [exact Hk|]. split; [exact Hkd|]. split; [exact Hl|].
  split; [lia|]. split; [exact Ha|]. split; [exact Htx|]. split; [exact Hka|]. split; [lia|]. split; [exact HW' | exact HAT'].
Qed.

(* one put run from the seat at pc to pc' (KST: a23_seat at the cut, KFIN: a23_end at it) *)
Ltac a23_go KST KFIN RUNTO HJ HAG HRL B32 pc' lo hi pl cs fv fe :=
  let HS := fresh "HS" in let SHOK := fresh "SHOK" in let HAWR := fresh "HAWR" in
  destruct (KST lo hi pl cs ltac:(lia) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
              ltac:(repeat (apply Forall_cons; [cbv beta; lia|]); apply Forall_nil)) as (HS & SHOK & HAWR);
  paj_run_to_tok RUNTO HS HJ SHOK k3_span (kpc pc'); [exact HAWR|];
  lazymatch goal with
  | HS' : st_ok_pi _ _ ?E ?ssx (restrict _ ?msn),
    HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ?msn)),
    HG' : mem_grows _ (mrestrict _ (ms_mem ?msn)) |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
    let HR1 := fresh "HR1" in
    spregion HS' 1%nat HR1;
    apply (KFIN lo hi pl cs ltac:(lia) ltac:(lia) msn mdn _ fe fv HR1 HFr' HG');
    [ assumption
    | apply (kn_kms_of _ E ssx msn pc' HS'); vm_compute; reflexivity
    | exact (regs_kept_of_st_ok_pi E ssx _ _ _ nx_keep0 HS' HAG ltac:(vm_compute; reflexivity))
    | intros r Hr;
      exact (regs_kept_of_st_ok_pi E ssx _ _ _ (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) [19; 21; 24; 22; 23; 27]%nat)
               HS' HAG ltac:(vm_compute; reflexivity) _ (kn_in_map5 r _ Hr))
    | rewrite (st_ok_pi_restrict_reg _ E ssx msn _ HS'); f_equal; vm_compute; reflexivity
    | first [ rewrite (st_ok_pi_restrict_reg _ E ssx msn _ HS');
              lazymatch goal with |- sv_denot _ ?t = _ => replace t with (SOff 32 0) by (vm_compute; reflexivity) end;
              cbn [sv_denot]; rewrite B32, Z.add_0_r; reflexivity
            | let Hk26 := fresh "Hk26" in
              pose proof (regs_kept_of_st_ok_pi E ssx _ _ _ (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) [26]%nat)
                            HS' HAG) as Hk26;
              specialize (Hk26 ltac:(vm_compute; reflexivity) _ (kn_in_map5 26 [26]%nat ltac:(kn_in)));
              first [rewrite Hk26 | etransitivity; [exact Hk26|]];
              apply (kn_reg_of _ _ 26 _ HRL); unfold a23_rl; kn_in ]
    | exact (proj1 (wvb_fds_fs _ _ _))
    | exact (proj2 (wvb_fds_fs _ _ _))
    | kn_in
    | kn_in
    | first [left; split; reflexivity | right; split; reflexivity] ]
  end.


(* ---- (H) THE PHASE: the nest's header ---- *)
Theorem a23_head : forall POST (Rc Rm Ra : kcx -> Z -> Prop),
  kfrom SK B POST (a23_at B Rc Rm Ra A23_J2) -> kfrom SK B POST (kin_acase B Rc Rm Ra KP_A23 ka_23).
Proof.
  intros POST Rc Rm Ra HN cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI.
  destruct HI as (qa & qp & Ha & Htx & (Hka & _) & HK).
  destruct HK as (qc & qci & qj & qm & qk & qn & qf & qadv & qhd & qkd & ql & HRc & HRm & HRa & Hc & Hci & Hj & Hm & Hk
    & Hkd & Hl & Hhd & HW & _ & HAT).
  pose proof HAT as (_ & HR0 & HRL & _ & _ & _ & _ & HJB & _).
  pose proof HB as ((_ & HGok & _) & _).
  pose proof HW as (_ & _ & _ & _ & _ & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  pose proof (kn_reg_of ms3 _ 21 (kW2 cx fpos) HRL ltac:(kn_in)) as R21.
  remember (Eimg (Ereg (ms_regs ms3) (k3_ext cx fpos qn qf qk))) as Eq3 eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM Eq3) by (rewrite HEdef; apply Eimg_env).
  assert (HAG : env_agree 32 (Ereg (ms_regs ms3) (k3_ext cx fpos qn qf qk)) Eq3)
    by (rewrite HEdef; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  destruct (k3_env SK B LAWS cx fpos k2 ly3 S3 md3 ms3 qn qf qk Eq3 HB HJB HR0 R21 ltac:(lia) Hfr ltac:(lia) HEdef)
    as (B9 & B20 & B21 & B32 & B33 & B34 & B35).
  pose proof (fun lo hi pl cs Hn Hpl Hnpl Hwf Hcs =>
    a23_seat SK B LAWS cx fpos k2 ly3 S3 W3 ms3 md3 KP_A23 _ _ qadv (Some qj) qn qf qk Eq3 HB HJ HW HAT
      ltac:(kn_in) ltac:(kn_in) ltac:(apply in_or_app; right; kn_in)
      ltac:(apply in_or_app; left; unfold kslots_setup; kn_in) ltac:(apply in_or_app; left; unfold kslots_setup; kn_in)
      ltac:(apply in_or_app; left; unfold kslots_setup; kn_in) ltac:(lia) HEdef lo hi pl cs [] Hn Hpl Hnpl Hwf Hcs I)
    as KST.
  pose proof (fun lo hi pl cs =>
    a23_end POST Rc Rm Ra cx fpos k2 ly3 S3 W3 ms3 md3 qc qci qj qm qk qn qf qadv qhd qkd ql qa qp qn KP_A23 _ Eq3
      lo hi pl cs [] A23_J2 HN HB HFR HRc HRm HRa Hc Hci Hj Hm Hk Hkd Hl Hhd Ha Htx Hka ltac:(lia) HW HAT
      ltac:(intros rv Hrv; cbn [In] in Hrv |- *; tauto) B21 B32 B33 B34) as KFIN.
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  destruct (Z_le_gt_dec qn 4092) as [G|G];
    [a23_go KST KFIN RUNTO HJ HAG HRL B32 A23_J2 0 4092 4 ([-4095; -4093]) qf (SOff 33 0)|].
  destruct (Z_le_gt_dec qn 4094) as [G'|G'];
    [a23_go KST KFIN RUNTO HJ HAG HRL B32 A23_J2 4093 4094 2 ([-4095]) 1 (SLit 1)|].
  a23_go KST KFIN RUNTO HJ HAG HRL B32 A23_J2 4095 4096 0 (@nil Z) 1 (SLit 1).
Qed.

(* `bne a1, 3`: a condition on a1's atom *)
Lemma a23_a1_cond : forall (E : env) (b : bool),
  (if b then bv_unsigned (ew E 11) = 3 else bv_unsigned (ew E 11) <> 3) ->
  conds_ok E [mkAC (if b then BC_EQ else BC_NE) (SOff 11 0) (SLit 3)].
Proof.
  intros E b H. cbn [conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
  pose proof (bv_unsigned_in_range 64 (ew E 11)) as Hr. change (bv_modulus 64) with M64 in Hr.
  destruct b; [rewrite branch_eq_U | rewrite branch_ne_U]; rewrite U_SOff, U_SLit, Z.add_0_r;
    rewrite (zcanon_id (bv_unsigned (ew E 11))) by exact Hr; rewrite (zcanon_id 3) by (unfold M64; lia).
  - apply Z.eqb_eq. exact H.
  - apply negb_true_iff, Z.eqb_neq. exact H.
Qed.

(* ---- (M) THE PHASE: `bne a1, 3`, and the nested attribute ---- *)
Theorem a23_mid : forall POST (Rc Rm Ra : kcx -> Z -> Prop),
  kfrom SK B POST (a23_at B Rc Rm Ra A23_J5) -> kfrom SK B POST (a23_at B Rc Rm Ra A23_J6) ->
  kfrom SK B POST (a23_at B Rc Rm Ra A23_J2).
Proof.
  intros POST Rc Rm Ra HN5 HN6 cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI.
  destruct HI as (qc & qci & qj & qm & qk & qn & qf & qadv & qhd & qkd & ql & qa & qp & qn0 & HRc & HRm & HRa & Hc
    & Hci & Hj & Hm & Hk & Hkd & Hl & Hhd & Ha & Htx & Hka & Hn0 & HW & HAT).
  pose proof HAT as (_ & HR0 & HRL & _ & _ & _ & _ & HJB & _).
  pose proof HB as ((_ & HGok & _) & _).
  pose proof HW as (_ & _ & _ & _ & _ & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  pose proof (kn_reg_of ms3 _ 21 (kW2 cx fpos) HRL ltac:(kn_in)) as R21.
  remember (Eimg (Ereg (ms_regs ms3) (k3_ext cx fpos qn qf qk))) as Eq3 eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM Eq3) by (rewrite HEdef; apply Eimg_env).
  assert (HAG : env_agree 32 (Ereg (ms_regs ms3) (k3_ext cx fpos qn qf qk)) Eq3)
    by (rewrite HEdef; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  destruct (k3_env SK B LAWS cx fpos k2 ly3 S3 md3 ms3 qn qf qk Eq3 HB HJB HR0 R21 ltac:(lia) Hfr ltac:(lia) HEdef)
    as (B9 & B20 & B21 & B32 & B33 & B34 & B35).
  pose proof (fun lo hi pl cs xc Hn Hpl Hnpl Hwf Hcs Hxc =>
    a23_seat SK B LAWS cx fpos k2 ly3 S3 W3 ms3 md3 A23_J2 _ _ qadv (Some qj) qn qf qk Eq3 HB HJ HW HAT
      ltac:(kn_in) ltac:(kn_in) ltac:(apply in_or_app; right; kn_in)
      ltac:(apply in_or_app; left; unfold kslots_setup; kn_in) ltac:(apply in_or_app; left; unfold kslots_setup; kn_in)
      ltac:(apply in_or_app; left; unfold kslots_setup; kn_in) ltac:(lia) HEdef lo hi pl cs xc Hn Hpl Hnpl Hwf Hcs Hxc)
    as KSTx.
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  destruct (Z.eq_dec (bv_unsigned (ew Eq3 11)) 3) as [H3 | H3].
  - (* a1 = 3: the nested attribute, to J5 *)
    pose proof (fun lo hi pl cs Hn Hpl Hnpl Hwf Hcs =>
      KSTx lo hi pl cs [mkAC BC_EQ (SOff 11 0) (SLit 3)] Hn Hpl Hnpl Hwf Hcs (a23_a1_cond Eq3 true H3)) as KST.
    pose proof (fun lo hi pl cs =>
      a23_end POST Rc Rm Ra cx fpos k2 ly3 S3 W3 ms3 md3 qc qci qj qm qk qn qf qadv qhd qkd ql qa qp qn0 A23_J2 _ Eq3
        lo hi pl cs [mkAC BC_EQ (SOff 11 0) (SLit 3)] A23_J5 HN5 HB HFR HRc HRm HRa Hc Hci Hj Hm Hk Hkd Hl Hhd Ha Htx Hka
        Hn0 HW HAT ltac:(intros rv Hrv; unfold a23_rl; cbn [In] in Hrv |- *; tauto) B21 B32 B33 B34) as KFIN.
    destruct (Z_le_gt_dec qn 4088) as [G|G];
      [a23_go KST KFIN RUNTO HJ HAG HRL B32 A23_J5 0 4088 8 ([-4095; -4093; -4089]) qf (SOff 33 0)|].
    destruct (Z_le_gt_dec qn 4092) as [G'|G'];
      [a23_go KST KFIN RUNTO HJ HAG HRL B32 A23_J5 4089 4092 4 ([-4095; -4093]) 1 (SLit 1)|].
    destruct (Z_le_gt_dec qn 4094) as [G''|G''];
      [a23_go KST KFIN RUNTO HJ HAG HRL B32 A23_J5 4093 4094 2 ([-4095]) 1 (SLit 1)|].
    a23_go KST KFIN RUNTO HJ HAG HRL B32 A23_J5 4095 4096 0 (@nil Z) 1 (SLit 1).
  - (* a1 <> 3: straight to J6 *)
    pose proof (fun lo hi pl cs Hn Hpl Hnpl Hwf Hcs =>
      KSTx lo hi pl cs [mkAC BC_NE (SOff 11 0) (SLit 3)] Hn Hpl Hnpl Hwf Hcs (a23_a1_cond Eq3 false H3)) as KST.
    pose proof (fun lo hi pl cs =>
      a23_end POST Rc Rm Ra cx fpos k2 ly3 S3 W3 ms3 md3 qc qci qj qm qk qn qf qadv qhd qkd ql qa qp qn0 A23_J2 _ Eq3
        lo hi pl cs [mkAC BC_NE (SOff 11 0) (SLit 3)] A23_J6 HN6 HB HFR HRc HRm HRa Hc Hci Hj Hm Hk Hkd Hl Hhd Ha Htx Hka
        Hn0 HW HAT ltac:(intros rv Hrv; unfold a23_rl; cbn [In] in Hrv |- *; tauto) B21 B32 B33 B34) as KFIN.
    a23_go KST KFIN RUNTO HJ HAG HRL B32 A23_J6 0 4096 0 (@nil Z) qf (SOff 33 0).
Qed.

End b.
End a.
