(* preset_base64_decode (fs.asan 0x8481c), part L of the Theorem Labs lane walk (a Theorem Labs lane): the loop 0x848bc from any head to
   the end (dec_stage_loop): the success arm returns into dec_post's third arm, a refused text reaches the call of
   fuzz_free (dec_at_free). Canonical states and the builder: FSW_dec_L0.v. SCRATCH part (owner a Theorem Labs lane). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSH_Fn_alloc FSH_Fn_writer
FSW_K FSW_ret FSW_rres FSW_writer_tbl FSW_writer_model.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSW_dec_defs FSW_dec_L0 FSW_dec_L1 FSW_dec_L2 FSW_dec_L3
  FSW_dec_L4 FSW_dec_L5.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterSpecFacts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section L. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HSS : FsShadowSyms B.

(* a Theorem Labs lane's memory facts (FSW_dec_L3.v) at this Section's B and CTX *)
Let XLB_text := decLB_text B.
Let XLB_q := decLB_q B.
Let XLB_keep := decLB_keep B.

(* the image facts (FSH_Rt.v:73-76) and the memchr interceptor's contract at fs.asan's PC_memchr (FSH_Gen.v:480,
   FSH_Rt.v FsRt.fr_memchr): the memchr arm FSW_dec_L4.decL_arm_other takes them *)
Hypothesis HIMG : fs_img_facts tfibsegs B.
Hypothesis HMEMCHR : amemchr_realizesU tfibsegs B PC_memchr.

Let decL_head_st := decL_head_st B HSS XLB_text XLB_q.

(* ---- one iteration from the head ---- *)
Definition decL_hcfg (regsc : bvmap 5 word) (memc : word -> option byte) (mdc : Model) : config :=
  mkCfg (YK11.mkst regsc (Z_to_bv 64 DEC_HEAD) memc (YK11.seg_rom tfibsegs)) mdc.

(* a run whose only write window is the loop frame [sp - 112, sp) changes no byte outside it *)
Lemma decL_fr_agree : forall Ex rs (H : word -> bool) m1 m2 lo hi,
  frame_of Ex rs (mrestrict H m1) (mrestrict H m2) ->
  (forall x, in_wrange Ex rs x -> lo <= x < hi) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview tfibsegs H m2 a = aview tfibsegs H m1 a.
Proof.
intros Ex rs H m1 m2 lo hi HF Hw a Ha Hna. unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite (wz a Ha). intros Hin. exact (Hna (Hw a Hin)).
Qed.
Lemma decL_agree_trans : forall (H : word -> bool) m1 m2 m3 lo hi,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview tfibsegs H m2 a = aview tfibsegs H m1 a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview tfibsegs H m3 a = aview tfibsegs H m2 a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview tfibsegs H m3 a = aview tfibsegs H m1 a.
Proof. intros H m1 m2 m3 lo hi H1 H2 a Ha Hna. rewrite (H2 a Ha Hna). exact (H1 a Ha Hna). Qed.

(* the write windows of a loop state: the frame region at atom 2, window [0, 112); every other region read-only *)
Definition decL_wchk (r : YP09.region) : bool :=
  match YP09.r_base r with
  | Some 2%nat => (YP09.r_wlo r =? 0) && (YP09.r_whi r =? 112)
  | _ => YP09.r_whi r <=? YP09.r_wlo r
  end.
Lemma decL_inw : forall Ex rs x b, forallb decL_wchk rs = true -> bv_unsigned (ew Ex 2) = b ->
  in_wrange Ex rs x -> b <= x < b + 112.
Proof.
intros Ex rs x b Hc Hb (r & Hin & Hx). pose proof (proj1 (forallb_forall _ _) Hc r Hin) as Hr.
unfold decL_wchk in Hr. destruct (YP09.r_base r) as [[|[|[|n]]]|] eqn:Eb;
  try (apply Z.leb_le in Hr; lia).
apply andb_prop in Hr as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2.
cbn [base_val] in Hx. try rewrite Eb in Hx. cbn [base_val] in Hx. rewrite Hb, H1, H2 in Hx. lia.
Qed.

(* the write window of the loop's runs: the frame region at atom 2 = sp - 112, window [0, 112), inside the journal's
   window [ot - STKJ, ot); every other region of the loop's states is read-only *)
Ltac decL_awr dd E2 Hspot HSTK :=
  cbn [add_cond ss_mem]; try (cbv [decL_hss fss_retT fsT_ret_regions app ss_mem]);
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := d_sp dd - DEC_F - d_ot dd);
  [ reflexivity
  | rewrite ?ew_ewset_other by lia; rewrite E2; lia
  | cbn; unfold d_STKJ, DEC_F in *; lia | cbn; unfold DEC_F in *; lia | ];
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

(* ---- the next loop head, from an engine state at DEC_HEAD after an iteration that stored nothing in the block ---- *)
Definition decL_kept_regs : list (bv 5) := [2; 3; 4; 8; 9; 19; 21; 25; 27]%bv.
Lemma decL_next : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k Ex SS ms md' six' pad' acc' ex,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (forall six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k',
     dec_head B d q (S i) six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k' ->
     SRr tfibsegs Wc' (decL_hcfg regsc' memc' mdc') (dec_post B d)) ->
  st_ok tfibsegs Ex SS (restrict (w_H Wc) ms) -> ss_resv SS = None -> ss_pc SS = DEC_HEAD ->
  nth_error (ss_mem SS) 0 = Some (fstk_ret DEC_F decL_cs) ->
  (forall n, (n < 47)%nat -> ew Ex n = ew (decL_E d regsc ex) n) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs SS) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) decL_kept_regs = true ->
  dec_J B d lyc Sc Wc Uc (ms_mem ms) md' k -> ARU tfibsegs B lyc Sc Uc Wc (ms_mem ms) md' ->
  decL_memf B d q six' Wc lyc Sc (ms_mem ms) ->
  getr (ms_regs ms) 18 = w64 (d_text d + Z.of_nat (S i)) -> getr (ms_regs ms) 20 = w64 (d_text d + Z.of_nat (S i)) ->
  getr (ms_regs ms) 22 = w64 (Z.of_nat (length (WriterSpec.six_bytes six'))) ->
  getr (ms_regs ms) 23 = w64 acc' -> 0 <= acc' < 2 ^ 64 ->
  getr (ms_regs ms) 24 = w64 (6 * Z.of_nat (length six') mod 8) -> getr (ms_regs ms) 26 = w64 pad' ->
  (S i <= length (d_tb d))%nat -> 0 <= pad' <= Z.of_nat (S i) -> (length six' <= S i)%nat ->
  Forall (fun x => 0 <= x < 64) six' -> acc' mod 64 = last six' 0 ->
  WriterSpec.b64_dec (d_tb d) = decLA_out pad' six' (skipn (S i) (d_tb d)) ->
  SRr tfibsegs Wc (mkCfg ms md') (dec_post B d).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k Ex SS ms md' six' pad' acc' ex HE HH HIH HS Hrv Hpc Hnth HEx
  Hkept HJ' HARU' HM' R18' R20' R22' R23' Hacc' R24' R26' Hi' Hpad' Hsix' Hsix64' Hlast' Hscan'.
pose proof (decL_lenp_range B d HE) as (L1 & L2 & _).
pose proof HH as HH0. decL_unhead HH.
assert (KR : forall r : bv 5, In r decL_kept_regs -> getr (ms_regs ms) r = getr regsc r).
{ intros r Hr. pose proof (proj1 (forallb_forall _ _) Hkept r Hr) as Hqq. apply sv_eqb_eq in Hqq.
  rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) Ex SS ms r HS), Hqq, fsw_SOff0.
  rewrite HEx by (cbv [decL_kept_regs In] in Hr;
    repeat (destruct Hr as [<-|Hr]; [vm_compute; lia|]); destruct Hr).
  unfold decL_E. apply ew_Ereg_nat. pose proof (u5_range r). rewrite Z2Nat.id by lia. reflexivity. }
assert (E2 : bv_unsigned (ew Ex 2) = d_sp d - DEC_F).
{ rewrite (HEx 2%nat ltac:(lia)). unfold decL_E. rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl). exact Hsp. }
destruct (decL_frame_back d regsc ex Wc ms Ex SS HS Hnth E2
  ltac:(intros n Hn; apply HEx; lia) ltac:(lia)) as [HFr' HLs'].
rewrite (st_ok_restrict_mkst tfibsegs (w_H Wc) Ex SS ms HS Hrv), Hpc.
apply (HIH six' pad' acc' Wc lyc Sc Uc (ms_regs ms) (ms_mem ms) md' k).
apply (decL_mk_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k (S i) six' pad' acc' (ms_regs ms) (ms_mem ms) md'
  HH0 HJ' HARU' HM' HFr' HLs').
- unfold spZ. rewrite (KR 2%bv ltac:(cbv; tauto)). exact Hsp.
- rewrite (KR 3%bv ltac:(cbv; tauto)). exact R3.
- rewrite (KR 4%bv ltac:(cbv; tauto)). exact R4.
- rewrite (KR 8%bv ltac:(cbv; tauto)). exact R8.
- rewrite (KR 9%bv ltac:(cbv; tauto)). exact R9.
- exact R18'.
- rewrite (KR 19%bv ltac:(cbv; tauto)). exact R19.
- exact R20'.
- rewrite (KR 21%bv ltac:(cbv; tauto)). exact R21.
- exact R22'.
- exact R23'.
- exact Hacc'.
- exact R24'.
- rewrite (KR 25%bv ltac:(cbv; tauto)). exact R25.
- exact R26'.
- rewrite (KR 27%bv ltac:(cbv; tauto)). exact R27.
- exact Hi'.
- exact Hpad'.
- exact Hsix'.
- exact Hsix64'.
- exact Hlast'.
- exact Hscan'.
Qed.

(* the runs' frames as one agreement of the memories outside the loop frame [lo, hi) *)
Ltac decL_agree E2 lo hi :=
  repeat match goal with
  | HF : frame_of ?Ex ?rs (mrestrict ?H ?m1) (mrestrict ?H ?m2) |- _ =>
      let A := fresh "AG" in
      assert (A : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview tfibsegs H m2 a = aview tfibsegs H m1 a);
      [ apply (decL_fr_agree Ex rs H m1 m2 lo hi HF);
        let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
        let Hw := fresh "Hw" in
        assert (Hw : lo <= x < lo + 112)
          by (apply (decL_inw Ex rs x lo); [vm_compute; reflexivity | rewrite ?ew_ewset_other by lia; rewrite E2; reflexivity
              | exact Hx]);
        unfold DEC_F in *; lia
      | clear HF ]
  end;
  repeat match goal with
  | A1 : forall a, _ -> _ -> aview tfibsegs ?H ?m2 a = aview tfibsegs ?H ?m1 a,
    A2 : forall a, _ -> _ -> aview tfibsegs ?H ?m3 a = aview tfibsegs ?H ?m2 a |- _ =>
      let A := fresh "AG" in pose proof (decL_agree_trans H m1 m2 m3 lo hi A1 A2) as A; clear A1 A2
  end.
(* a register the iteration left as at the head *)
Ltac decL_rkeep E HSF n r Rn :=
  eapply (decL_reg _ _ _ _ r (SOff n 0));
  [ exact HSF | vm_compute; reflexivity
  | rewrite fsw_SOff0, ?ew_ewset_other by lia; unfold E; rewrite (decL_E_reg _ _ _ n r eq_refl); exact Rn ].
(* a register the iteration left as SOff n z, worth v + z *)
Ltac decL_rplus E HSF n z r Rn :=
  eapply (decL_reg _ _ _ _ r (SOff n z));
  [ exact HSF | vm_compute; reflexivity
  | apply decL_soff;
    [ rewrite ?ew_ewset_other by lia; unfold E; rewrite (decL_E_reg _ _ _ n r eq_refl); exact Rn | lia | lia ] ].

Lemma decL_arm_skip : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (forall six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k',
     dec_head B d q (S i) six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k' ->
     SRr tfibsegs Wc' (decL_hcfg regsc' memc' mdc') (dec_post B d)) ->
  (i < length (d_tb d))%nat ->
  WriterSpec.b64_ws (nth i (d_tb d) 0) = true \/ nth i (d_tb d) 0 = 61 ->
  SRr tfibsegs Wc (decL_hcfg regsc memc mdc) (dec_post B d).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH HIH Hlt Hcase.
destruct (decL_head_st d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH) as [HS SHOK].
pose proof HH as HH0. decL_unhead HH. unfold dec_J in HJ.
assert (HSTK : 112 <= STK_preset_base64_decode) by (vm_compute; discriminate).
assert (Hspot : d_sp d <= d_ot d).
{ destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPL).
  unfold d_sp. destruct HPL as [(_ & H1 & H2 & _) | (_ & H1 & _)]; lia. }
assert (Hc : nth i (d_tb d ++ [0]) 0 = nth i (d_tb d) 0) by (rewrite app_nth1 by exact Hlt; reflexivity).
set (c := nth i (d_tb d ++ [0]) 0) in *.
assert (Hc61 : c <= 61).
{ rewrite Hc. destruct Hcase as [Hw | ->]; [|lia].
  destruct (decLA_ws_vals _ Hw) as [ -> | [ -> | [ -> | -> ]]]; lia. }
set (E := decL_E d regsc [Z_to_bv 64 c]) in *.
assert (E47 : ew E 47 = Z_to_bv 64 c) by (unfold E; exact (decL_E_ex d regsc _ 0)).
assert (E25 : ew E 25 = Z_to_bv 64 61) by (unfold E; rewrite (decL_E_reg d regsc _ 25 25%bv eq_refl), R25; reflexivity).
assert (E8 : ew E 8 = Z_to_bv 64 DEC_WSMASK) by (unfold E; rewrite (decL_E_reg d regsc _ 8 8%bv eq_refl), R8; reflexivity).
pose proof (decL_text_byte d Wc memc i (proj1 (proj2 (proj2 HKe))) Hi) as (_ & Rc). fold c in Rc.
assert (E2 : bv_unsigned (ew E 2) = d_sp d - DEC_F)
  by (unfold E; rewrite (decL_E_reg d regsc _ 2 2%bv eq_refl); exact Hsp).
unfold decL_hcfg.
fsw_aj_run_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan.
{ decL_awr d E2 Hspot HSTK. }
(* 0x848d0: bltu s9, c -- not taken, c <= 61 *)
eapply SRr_sym_branch with (c := BC_LTU) (a := SOff 25 0) (b := SOff 47 0); [exact HS | intros Hb0 _ | intros Hb0 HS2].
{ exfalso. rewrite (decLA_br_ltu _ 25 47 61 c) in Hb0;
    [apply Z.ltb_lt in Hb0; lia | rewrite !ew_ewset_other by lia; exact E25
    | rewrite !ew_ewset_other by lia; exact E47 | lia | lia]. }
clear HS Hb0.
fsw_aj_run_tokU fsw_wr_tbl_ok HS2 HJ HARU SHOK fs_Bspan.
{ decL_awr d E2 Hspot HSTK. }
(* 0x848dc: (mask >> c) & 1 *)
pose proof (fsw_sp B _ _ _ _ _ _ _ _ _ (proj1 (proj1 HE))) as (_ & Hsp1 & _ & _).
pose proof (XLB_text d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH0) as (T1 & T2 & _).
pose proof asan_consts as (C1 & _ & _ & _).
assert (Hlo : alloc_ceiling <= d_sp d - DEC_F) by (unfold d_sp, DEC_F; lia).
assert (HM0 : decL_memf B d q six Wc lyc Sc memc) by (split; [exact Hrb | split; [exact Hra | split; [exact Hglob | split; [exact HKe | exact HZb]]]]).
pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & Htb & _).
assert (Hscan0 : WriterSpec.b64_dec (d_tb d) = decLA_out pad six (nth i (d_tb d) 0 :: skipn (S i) (d_tb d)))
  by (rewrite <- (decLA_skipn (d_tb d) i Hlt); exact Hscan).
eapply SRr_sym_branch with (c := BC_NE) (a := SAlu ALU_AND (SAlu ALU_SRL (SOff 8 0) (SOff 47 0)) (SLit 1)) (b := SLit 0);
  [exact HS2 | intros Hb HS3 | intros Hb HS3];
  rewrite (decLA_br_ws _ 8 47 c) in Hb by (rewrite ?ew_ewset_other by lia; first [exact E8 | exact E47 | lia]);
  clear HS2.
- (* whitespace: the next byte *)
  fsw_aj_run_to_tokU fsw_wr_tbl_ok HS3 HJ HARU SHOK fs_Bspan DEC_HEAD.
  { decL_awr d E2 Hspot HSTK. }
  decL_agree E2 (d_sp d - DEC_F) (d_sp d).

  match goal with AG : forall a, _ -> _ -> aview _ _ ?mF a = aview _ _ memc a |- _ =>
    pose proof (XLB_keep d q i six pad acc Wc lyc Sc Uc regsc memc mdc k memc mF (d_sp d - DEC_F) (d_sp d) HE HH0 HM0
      Hlo ltac:(lia) AG) as HMF end.
  eapply (decL_next d q i six pad acc Wc lyc Sc Uc regsc memc mdc k _ _ _ _ six pad acc [Z_to_bv 64 c] HE HH0 HIH HS3);
    [ reflexivity | reflexivity | vm_compute; reflexivity
    | intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity | vm_compute; reflexivity
    | exact HJ | exact HARU | exact HMF | .. ].
  + rewrite Nat2Z.inj_succ, Z.add_succ_r, <- Z.add_1_r.
    decL_rplus E HS3 18%nat 1 (18%bv : bv 5) R18.
  + rewrite Nat2Z.inj_succ, Z.add_succ_r, <- Z.add_1_r. decL_rplus E HS3 20%nat 1 (20%bv : bv 5) R20.
  + decL_rkeep E HS3 22%nat (22%bv : bv 5) R22.
  + decL_rkeep E HS3 23%nat (23%bv : bv 5) R23.
  + exact Hacc.
  + decL_rkeep E HS3 24%nat (24%bv : bv 5) R24.
  + decL_rkeep E HS3 26%nat (26%bv : bv 5) R26.
  + lia.
  + lia.
  + lia.
  + exact Hsix64.
  + exact Hlast.
  + rewrite Hscan0. rewrite <- Hc. apply decLA_out_ws. exact Hb.
- (* not whitespace: c = 61 *)
  assert (Hc61' : c = 61) by (destruct Hcase as [Hw | H61]; [rewrite <- Hc, Hb in Hw; discriminate Hw | rewrite Hc; exact H61]).
  fsw_aj_run_tokU fsw_wr_tbl_ok HS3 HJ HARU SHOK fs_Bspan.
  { decL_awr d E2 Hspot HSTK. }
  (* 0x848e0: c <> 61 -- not taken *)
  eapply SRr_sym_branch with (c := BC_NE) (a := SOff 47 0) (b := SOff 25 0); [exact HS3 | intros Hb2 _ | intros Hb2 HS4].
  { exfalso. rewrite (decLA_br_ne _ 47 25 c 61) in Hb2
      by (rewrite ?ew_ewset_other by lia; first [exact E47 | exact E25 | lia]).
    rewrite Hc61', Z.eqb_refl in Hb2. discriminate Hb2. }
  clear HS3.
  fsw_aj_run_to_tokU fsw_wr_tbl_ok HS4 HJ HARU SHOK fs_Bspan DEC_HEAD.
  { decL_awr d E2 Hspot HSTK. }
  decL_agree E2 (d_sp d - DEC_F) (d_sp d).
  match goal with AG : forall a, _ -> _ -> aview _ _ ?mF a = aview _ _ memc a |- _ =>
    pose proof (XLB_keep d q i six pad acc Wc lyc Sc Uc regsc memc mdc k memc mF (d_sp d - DEC_F) (d_sp d) HE HH0 HM0
      Hlo ltac:(lia) AG) as HMF end.
  eapply (decL_next d q i six pad acc Wc lyc Sc Uc regsc memc mdc k _ _ _ _ six (pad + 1) acc [Z_to_bv 64 c] HE HH0 HIH
    HS4);
    [ reflexivity | reflexivity | vm_compute; reflexivity
    | intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity | vm_compute; reflexivity
    | exact HJ | exact HARU | exact HMF | .. ].
  + rewrite Nat2Z.inj_succ, Z.add_succ_r, <- Z.add_1_r. decL_rplus E HS4 18%nat 1 (18%bv : bv 5) R18.
  + rewrite Nat2Z.inj_succ, Z.add_succ_r, <- Z.add_1_r. decL_rplus E HS4 20%nat 1 (20%bv : bv 5) R20.
  + decL_rkeep E HS4 22%nat (22%bv : bv 5) R22.
  + decL_rkeep E HS4 23%nat (23%bv : bv 5) R23.
  + exact Hacc.
  + decL_rkeep E HS4 24%nat (24%bv : bv 5) R24.
  + decL_rplus E HS4 26%nat 1 (26%bv : bv 5) R26.
  + lia.
  + lia.
  + lia.
  + exact Hsix64.
  + exact Hlast.
  + rewrite Hscan0. rewrite <- Hc, Hc61'. apply decLA_out_61.
Qed.

(* ---- one iteration: the byte decides the arm ---- *)
Lemma decL_head_i : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k,
  dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k -> (i <= length (d_tb d))%nat.
Proof. intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH. decL_unhead HH. exact Hi. Qed.


Lemma decL_step : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (forall W3 ly3 S3 U3 regs3 mem3 md3 k3, dec_at_free B d q W3 ly3 S3 U3 regs3 mem3 md3 k3 ->
     SRr tfibsegs W3 (cfg_at tfibsegs A_fuzz_free regs3 mem3 md3) (dec_post B d)) ->
  (forall six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k',
     dec_head B d q (S i) six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k' ->
     SRr tfibsegs Wc' (decL_hcfg regsc' memc' mdc') (dec_post B d)) ->
  ((i = length (d_tb d))%nat ->
     SRr tfibsegs Wc (decL_hcfg regsc memc mdc) (dec_post B d)) ->
  SRr tfibsegs Wc (decL_hcfg regsc memc mdc) (dec_post B d).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH HFREE HIH HNUL.
pose proof (decL_head_i d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH) as Hi.
destruct (Nat.eq_dec i (length (d_tb d))) as [Heq | Hne]; [exact (HNUL Heq)|].
assert (Hlt : (i < length (d_tb d))%nat) by lia.
destruct (WriterSpec.b64_ws (nth i (d_tb d) 0)) eqn:Ew.
- exact (decL_arm_skip d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH HIH Hlt (or_introl Ew)).
- destruct (Z.eq_dec (nth i (d_tb d) 0) 61) as [E61 | N61].
  + exact (decL_arm_skip d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH HIH Hlt (or_intror E61)).
  + exact (decL_arm_other B HSS HIMG HMEMCHR d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH HFREE HIH Hlt
      Ew N61).
Qed.

(* ---- the loop, by induction on the bytes left ---- *)
Lemma decL_loop_gen : forall (P : DE -> Prop),
  (forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k, P d ->
     dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
     (forall W3 ly3 S3 U3 regs3 mem3 md3 k3, dec_at_free B d q W3 ly3 S3 U3 regs3 mem3 md3 k3 ->
        SRr tfibsegs W3 (cfg_at tfibsegs A_fuzz_free regs3 mem3 md3) (dec_post B d)) ->
     i = length (d_tb d) -> SRr tfibsegs Wc (decL_hcfg regsc memc mdc) (dec_post B d)) ->
  forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k, P d ->
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (forall W3 ly3 S3 U3 regs3 mem3 md3 k3, dec_at_free B d q W3 ly3 S3 U3 regs3 mem3 md3 k3 ->
     SRr tfibsegs W3 (cfg_at tfibsegs A_fuzz_free regs3 mem3 md3) (dec_post B d)) ->
  SRr tfibsegs Wc (decL_hcfg regsc memc mdc) (dec_post B d).
Proof.
intros P HNUL d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HP HE HH HFREE.
remember (length (d_tb d) - i)%nat as m eqn:Hm.
revert i six pad acc Wc lyc Sc Uc regsc memc mdc k HH Hm.
induction m as [|m IH]; intros i six pad acc Wc lyc Sc Uc regsc memc mdc k HH Hm.
- apply (decL_step d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH HFREE).
  + intros six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k' HH'.
    pose proof (decL_head_i d q (S i) six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k' HH') as Hi'. lia.
  + intros Heq. exact (HNUL d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HP HE HH HFREE Heq).
- apply (decL_step d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH HFREE).
  + intros six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k' HH'.
    apply (IH (S i) six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k' HH'). lia.
  + intros Heq. exact (HNUL d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HP HE HH HFREE Heq).
Qed.

(* the stage, both placements of the length slot (decode_spec and decode_spec_ff) *)
Lemma dec_loop_stage : dec_stage_loop B.
Proof.
unfold dec_stage_loop. intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH HFREE.
refine (decL_loop_gen (fun _ => True) _ d q i six pad acc Wc lyc Sc Uc regsc memc mdc k I HE HH HFREE).
intros d0 q0 i0 six0 pad0 acc0 Wc0 lyc0 Sc0 Uc0 regsc0 memc0 mdc0 k0 _ HE0 HH0 HFREE0 Heq.
exact (decL_arm_nul B HSS d0 q0 i0 six0 pad0 acc0 Wc0 lyc0 Sc0 Uc0 regsc0 memc0 mdc0 k0 HE0 HH0 HFREE0 Heq).
Qed.
End L.
