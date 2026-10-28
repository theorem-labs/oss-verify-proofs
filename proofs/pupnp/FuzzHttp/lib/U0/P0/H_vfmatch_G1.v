(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_ctype H_scanner_get_token H_vfmatch_A H_vfmatch_B H_vfmatch_F HU_vfm_ws HU_vfm_lit HU_vfm_R.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Ltac sstep := step; fix_lit_store.

Ltac split_chunk FR n H1 H2 :=
  lazymatch type of FR with rw_cells ?segs ?m ?A ?cs =>
    let cs1 := eval cbv beta iota delta [firstn skipn] in (firstn n cs) in
    let cs2 := eval cbv beta iota delta [firstn skipn] in (skipn n cs) in
    change (rw_cells segs m A (cs1 ++ cs2)) in FR;
    destruct (proj1 (rw_cells_app segs m A cs1 cs2) FR) as [H1 H2]; clear FR;
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in H2;
    try (lazymatch type of H2 with rw_cells _ _ (?a + ?b + ?c)%Z _ =>
           let v := eval vm_compute in (b + c)%Z in replace (a + b + c)%Z with (a + v)%Z in H2 by lia end)
  end.

Ltac recell FR i :=
  lazymatch type of FR with rw_cells ?segs ?m ?A ?cs =>
    let pre := eval cbv beta iota delta [firstn skipn] in (firstn i cs) in
    let post := eval cbv beta iota delta [firstn skipn] in (skipn (S i) cs) in
    lazymatch eval cbv beta iota delta [firstn skipn nth_error] in (nth_error cs i) with
    | Some (CB 8 ?b) => change (rw_cells segs m A (pre ++ CB 8 b :: post)) in FR; apply (rw_cells_CB_C8 segs m A pre b post) in FR; cbn [app] in FR
    | Some (CB 4 ?b) => change (rw_cells segs m A (pre ++ CB 4 b :: post)) in FR; apply (rw_cells_CB_C4 segs m A pre b post) in FR; cbn [app] in FR
    end end.

Ltac splitcb FR i sizes :=
  lazymatch type of FR with rw_cells ?segs ?m ?A ?cs =>
    let pre := eval cbv beta iota delta [firstn skipn] in (firstn i cs) in
    let post := eval cbv beta iota delta [firstn skipn] in (skipn (S i) cs) in
    lazymatch eval cbv beta iota delta [firstn skipn nth_error] in (nth_error cs i) with
    | Some (CB ?n ?b) => change (rw_cells segs m A (pre ++ CB n b :: post)) in FR;
        apply (rw_cells_split_CB segs m A pre n b post sizes) in FR; [| reflexivity]; cbn [app mk_CB_cells] in FR
    end end.

Ltac name_junk FR :=
  repeat lazymatch type of FR with context [CB _ (firstn ?a ?b)] => let j := fresh "jk" in remember (firstn a b) as j in FR
                      | context [CB _ (skipn ?a ?b)] => let j := fresh "jk" in remember (skipn a b) as j in FR end;
  repeat match goal with E : _ = firstn _ _ |- _ => clear E | E : _ = skipn _ _ |- _ => clear E end.

Section VFG.
Context {HCEIL : HasCeiling}.
  Variables (q lo S MB A len cap cur0 : Z) (bs : list byte).
  Hypothesis VOK : vf_ok q lo S MB A len cap cur0 bs.

  Notation qq := (q + -208)%Z.
  Notation W0 := [(q - 304, q - 104); (S + 8, S + 16)]%Z.
  Notation dpost := (dpost q lo S MB A len cap cur0 bs).
  Notation linv := (linv q lo S MB A len cap bs).
  Notation headst := (headst q S cur0). Notation contst := (contst q S cur0). Notation exitst := (exitst q S cur0).
  Notation SCc := (SCc S MB). Notation MBc := (MBc MB A len cap). Notation BUFc := (BUFc A bs). Notation FX := (FX q).
  Notation F0 := (F0 q). Notation F36 := (F36 q). Notation F40 := (F40 q). Notation F56 := (F56 q).
  Notation F72 := (F72 q). Notation F76 := (F76 q). Notation F84 := (F84 q). Notation F88 := (F88 q).
  Ltac sgtcall T TY cur := sgtcall_ (q + -208)%Z lo S T TY MB A cur len cap bs.
  Notation WF Wx := ((lo, q) :: (S + 8, S + 16) :: Wx)%Z.
  Notation vpost := (vpost q lo S MB A len cap cur0 bs).
  Notation FS := (FS q).

  Notation FMT_CRLF := 0x102ea%Z.
  Definition fb_crlf : list byte := map (Z_to_bv 8) [37; 99; 0].
  #[using="Type"] Lemma fb_crlf_at : forall m, mem_inv rsegs m -> bytes_at rsegs m FMT_CRLF fb_crlf.
  Proof.
    intros m MI. pose proof (ro_cells_image rsegs m FMT_CRLF fb_crlf MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO.
    destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
  Qed.
  Ltac rd_crlf := rdfmt fb_crlf_at constr:(0x102ea%Z).

  #[using="VOK"] Theorem vf_crlf : forall (G : Z) ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m,
    stk rsegs m lo q -> mem_inv rsegs m -> SCc m cur0 -> MBc m -> BUFc m -> (q + 16 <= G <= q + 64)%Z ->
    evt rsegs (vpost ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (WF [])
                 (fun m' r cur' => True /\ (r = PARSE_OK -> cur0 + 1 <= cur')%Z) m)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz S) (wz FMT_CRLF) (wz G) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz vfmatch_entry) fc None m (seg_rom rsegs)).
  Proof.
    pose proof VOK as VOK'. vok VOK'.
    intros until m. intros ST MI SC MBC BUF GR. unfx.
    pose proof (munch_refl (WF []) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    eapply evt_cut.
    { eapply (prologue q lo S MB A len cap cur0 bs VOK FMT_CRLF 37 G (Z_to_bv 8 37)); try eassumption; try reflexivity; try lia.
      intros m1 MI1. rd_crlf. }
    post_call rsegs m. rename PC into ST. rename PC0 into FSH. rename POST into F0P. lazymatch goal with H : H_vfmatch_A.FX _ _ |- _ => rename H into FXH end. open_FX FXH. clear FR0. destruct F0P as [? FR0]. unfold H_vfmatch_A.F0 in FR0. dex. unfold FS in FSH.
    dcall (dir_c q lo S MB A len cap cur0 bs VOK) r1 c1 X1; [rd_crlf| reflexivity| |].
    -   destruct (Z.eq_dec r1 PARSE_OK) as [->|NE].
      + eapply cont_end with (R := fun _ => True); try eassumption; try rd_crlf; try reflexivity; try exact I; try (unfold PARSE_OK in *; lia).
        all: match goal with |- ?G => idtac G end.
      + eapply cont_err with (R := fun _ => True); try eassumption; try rd_crlf; try exact I; try (unfold PARSE_OK in *; lia).
        unfold rframe; intros; exact I.
    -   exfalso; exact HXE.
  Qed.

  Notation FMT_HDR := 0x102e5%Z.
  Definition fb_hdr : list byte := map (Z_to_bv 8) [32; 58; 32; 37; 82; 37; 99; 0].
  #[using="Type"] Lemma fb_hdr_at : forall m, mem_inv rsegs m -> bytes_at rsegs m FMT_HDR fb_hdr.
  Proof.
    intros m MI. pose proof (ro_cells_image rsegs m FMT_HDR fb_hdr MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO.
    destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
  Qed.
  Ltac rd_hdr := rdfmt fb_hdr_at constr:(0x102e5%Z).

  Definition X_hdr (P1 : Z) : mem -> Z -> Z -> Prop := fun m' r cur' =>
    (exists pa pb, rw_cells rsegs m' P1 [C8 pa; C8 pb]
       /\ (r = PARSE_OK -> exists o l, pa = wz (A + o) /\ pb = wz l /\ cur0 <= o /\ 0 <= l /\ o + l <= len /\ cur0 + 1 <= cur' /\ o + l <= cur' + 1))%Z.

  #[using="VOK"] Theorem vf_hdr : forall (P1 : Z) (pw1 pw2 : word) ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m,
    stk rsegs m lo q -> mem_inv rsegs m -> SCc m cur0 -> MBc m -> BUFc m ->
    rw_cells rsegs m (q + 16) [C8 (wz P1)] -> rw_cells rsegs m P1 [C8 pw1; C8 pw2] -> (q + 64 <= P1 /\ P1 + 16 <= MB)%Z -> (P1 mod 8 = 0)%Z ->
    evt rsegs (vpost ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (WF [(P1, P1 + 16)]%Z) (X_hdr P1) m)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz S) (wz FMT_HDR) (wz (q + 16)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz vfmatch_entry) fc None m (seg_rom rsegs)).
  Proof.
    pose proof VOK as VOK'. vok VOK'.
    intros until m. intros ST MI SC MBC BUF GC1 PC1 PL1 PA1. unfx.
    pose proof (munch_refl (WF [(P1, P1 + 16)]%Z) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    eapply evt_cut.
    { eapply (prologue q lo S MB A len cap cur0 bs VOK FMT_HDR 32 (q + 16) (Z_to_bv 8 32)); try eassumption; try reflexivity; try lia. intros m1 MI1. rd_hdr. }
    post_call rsegs m. rename PC into ST. rename PC0 into FSH. rename POST into F0P. lazymatch goal with H : H_vfmatch_A.FX _ _ |- _ => rename H into FXH end. open_FX FXH. clear FR0. destruct F0P as [? FR0]. unfold H_vfmatch_A.F0 in FR0. dex. unfold FS in FSH.

    Ltac hdr_err P1 :=
      lazymatch goal with PCH : rw_cells rsegs _ P1 [C8 ?pa; C8 ?pb] |- _ =>
      eapply evt_mono;
      [ first [ eapply cont_err with (R := fun mm => rw_cells rsegs mm P1 [C8 pa; C8 pb]) (XP := fun r c => r <> PARSE_OK)
              | eapply tail_err with (R := fun mm => rw_cells rsegs mm P1 [C8 pa; C8 pb]) (XP := fun r c => r <> PARSE_OK) ];
        try eassumption; try rd_hdr; try (unfold PARSE_OK in *; lia);
        unfold rframe; intros mA mB HRR MUR WMR; rf1 HRR MUR WMR
      | intros ms' V; eapply vpost_mono; [| exact V]; cbn beta; intros mm rr cc [HRm HXP];
        unfold X_hdr; do 2 eexists; split; [exact HRm|]; let E := fresh in intros E; exfalso; exact (HXP E) ] end.

    dcall (dir_sp q lo S MB A len cap cur0 bs VOK) r1 c1 X1.
    2:{ exfalso; exact HXE. }
    destruct (Z.eq_dec r1 PARSE_OK) as [->|NE]; [| hdr_err P1].
    eapply (cont_next q lo S MB A len cap cur0 bs VOK _ 58); [rd_hdr| reflexivity| lia| lia|]. open_FX FXH. clear FR0. destruct F0H as [? FR0]. unfold H_vfmatch_A.F0 in FR0. dex.

    dcall (dir_lit q lo S MB A len cap cur0 bs VOK) r2 c2 X2.
    2:{ exfalso; exact HXE. }
    destruct (Z.eq_dec r2 PARSE_OK) as [->|NE]; [| hdr_err P1].
    eapply (cont_next q lo S MB A len cap cur0 bs VOK _ 32); [rd_hdr| reflexivity| lia| lia|]. open_FX FXH. clear FR0. destruct F0H as [? FR0]. unfold H_vfmatch_A.F0 in FR0. dex.

    dcall (dir_sp q lo S MB A len cap cur0 bs VOK) r3 c3 X3.
    2:{ exfalso; exact HXE. }
    destruct (Z.eq_dec r3 PARSE_OK) as [->|NE]; [| hdr_err P1].
    eapply (cont_next q lo S MB A len cap cur0 bs VOK _ 37); [rd_hdr| reflexivity| lia| lia|]. open_FX FXH. clear FR0. destruct F0H as [? FR0]. unfold H_vfmatch_A.F0 in FR0. dex.

    dcall (dir_R q lo S MB A len cap cur0 bs VOK) r4 c4 X4; [rd_hdr| reflexivity| |].
    2:{ exfalso; exact HXE. }
    unfold XR in X4; destruct X4 as (pa & pb & PC1 & HXR).
    destruct (Z.eq_dec r4 PARSE_OK) as [->|NE]; [| hdr_err P1].
    destruct (HXR eq_refl) as (l & -> & -> & L0 & LB & C34).
    eapply (cont_next q lo S MB A len cap cur0 bs VOK _ 37); [rd_hdr| reflexivity| lia| lia|]. open_FX FXH. clear FR0. destruct F0H as [? FR0]. unfold H_vfmatch_A.F0 in FR0. dex.

    dcall (dir_c q lo S MB A len cap cur0 bs VOK) r5 c5 X5; [rd_hdr| reflexivity| |].
    2:{ exfalso; exact HXE. }
    destruct (Z.eq_dec r5 PARSE_OK) as [->|NE]; [| hdr_err P1].
    eapply evt_mono.
    { eapply cont_end with (R := fun mm => rw_cells rsegs mm P1 [C8 (wz (A + c3)); C8 (wz l)])
                            (XP := (fun r c => r = PARSE_OK -> cur0 <= c3 /\ 0 <= l /\ c3 + l <= len /\ cur0 + 1 <= c /\ c3 + l <= c + 1)%Z);
      try eassumption; try rd_hdr; try reflexivity; try (unfold PARSE_OK in *; lia). }
    intros ms' V; eapply vpost_mono; [| exact V]; cbn beta; intros mm rr cc [HRm HXP].
    unfold X_hdr. do 2 eexists; split; [exact HRm|]. intros E. exists c3, l. pose proof (HXP E). use_ok. repeat split; try reflexivity; lia.
  Qed.

  Notation FMT_RESP := 0x10646%Z.
  Definition fb_resp : list byte := map (Z_to_bv 8) [37; 105; 104; 116; 116; 112; 37; 119; 47; 37; 119; 37; 76; 37; 99; 0].
  #[using="Type"] Lemma fb_resp_at : forall m, mem_inv rsegs m -> bytes_at rsegs m FMT_RESP fb_resp.
  Proof.
    intros m MI. pose proof (ro_cells_image rsegs m FMT_RESP fb_resp MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO.
    destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
  Qed.
  Ltac rd_resp := rdfmt fb_resp_at constr:(0x10646%Z).

  Definition X_resp (P1 : Z) : mem -> Z -> Z -> Prop := fun m' r cur' =>
    (exists pa pb, rw_cells rsegs m' P1 [C8 pa; C8 pb]
       /\ (r = PARSE_OK -> exists o l, pa = wz (A + o) /\ pb = wz l /\ cur0 <= o /\ 0 <= l /\ o + l < cur' /\ cur' <= len
             /\ exists b, nth_error bs (Z.to_nat (o + l)) = Some b /\ (bv_unsigned b = 13 \/ bv_unsigned b = 10)))%Z.

  #[using="VOK"] Theorem vf_resp : forall (P1 : Z) (pw1 pw2 : word) ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m,
    stk rsegs m lo q -> mem_inv rsegs m -> SCc m cur0 -> MBc m -> BUFc m ->
    rw_cells rsegs m (q + 16) [C8 (wz P1)] -> rw_cells rsegs m P1 [C8 pw1; C8 pw2] -> (q + 64 <= P1 /\ P1 + 16 <= MB)%Z -> (P1 mod 8 = 0)%Z ->
    evt rsegs (vpost ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (WF [(P1, P1 + 16)]%Z) (X_resp P1) m)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz S) (wz FMT_RESP) (wz (q + 16)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz vfmatch_entry) fc None m (seg_rom rsegs)).
  Proof.
    pose proof VOK as VOK'. vok VOK'.
    intros until m. intros ST MI SC MBC BUF GC1 PC1 PL1 PA1. unfx.
    pose proof (munch_refl (WF [(P1, P1 + 16)]%Z) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    eapply evt_cut.
    { eapply (prologue q lo S MB A len cap cur0 bs VOK FMT_RESP 37 (q + 16) (Z_to_bv 8 37)); try eassumption; try reflexivity; try lia. intros m1 MI1. rd_resp. }
    post_call rsegs m. rename PC into ST. rename PC0 into FSH. rename POST into F0P. lazymatch goal with H : H_vfmatch_A.FX _ _ |- _ => rename H into FXH end. open_FX FXH. clear FR0. destruct F0P as [? FR0]. unfold H_vfmatch_A.F0 in FR0. dex. unfold FS in FSH.

    dcall (dir_i q lo S MB A len cap cur0 bs VOK) r1 c1 X1; [rd_resp| reflexivity| |]. 2:{ exfalso; exact HXE. }
    destruct X1 as [-> ->].
    eapply (cont_next q lo S MB A len cap cur0 bs VOK _ 104); [rd_resp| reflexivity| lia| lia|]. open_FX FXH. clear FR0. destruct F0H as [? FR0]. unfold H_vfmatch_A.F0 in FR0. dex.

    dcall (dir_lit q lo S MB A len cap cur0 bs VOK) r2 c2 X2. 2:{ exfalso; exact HXE. }
    destruct (Z.eq_dec r2 PARSE_OK) as [->|NE]; [| err1 P1 fb_resp_at constr:(0x10646%Z) X_resp].
    eapply (cont_next q lo S MB A len cap cur0 bs VOK _ 116); [rd_resp| reflexivity| lia| lia|]. open_FX FXH. clear FR0. destruct F0H as [? FR0]. unfold H_vfmatch_A.F0 in FR0. dex.
    dcall (dir_lit q lo S MB A len cap cur0 bs VOK) r3 c3 X3. 2:{ exfalso; exact HXE. }
    destruct (Z.eq_dec r3 PARSE_OK) as [->|NE]; [| err1 P1 fb_resp_at constr:(0x10646%Z) X_resp].
    eapply (cont_next q lo S MB A len cap cur0 bs VOK _ 116); [rd_resp| reflexivity| lia| lia|]. open_FX FXH. clear FR0. destruct F0H as [? FR0]. unfold H_vfmatch_A.F0 in FR0. dex.
    dcall (dir_lit q lo S MB A len cap cur0 bs VOK) r4 c4 X4. 2:{ exfalso; exact HXE. }
    destruct (Z.eq_dec r4 PARSE_OK) as [->|NE]; [| err1 P1 fb_resp_at constr:(0x10646%Z) X_resp].
    eapply (cont_next q lo S MB A len cap cur0 bs VOK _ 112); [rd_resp| reflexivity| lia| lia|]. open_FX FXH. clear FR0. destruct F0H as [? FR0]. unfold H_vfmatch_A.F0 in FR0. dex.
    dcall (dir_lit q lo S MB A len cap cur0 bs VOK) r5 c5 X5. 2:{ exfalso; exact HXE. }
    destruct (Z.eq_dec r5 PARSE_OK) as [->|NE]; [| err1 P1 fb_resp_at constr:(0x10646%Z) X_resp].
    eapply (cont_next q lo S MB A len cap cur0 bs VOK _ 37); [rd_resp| reflexivity| lia| lia|]. open_FX FXH. clear FR0. destruct F0H as [? FR0]. unfold H_vfmatch_A.F0 in FR0. dex.

    dcall (dir_w q lo S MB A len cap cur0 bs VOK) r6 c6 X6; [rd_resp| reflexivity| |]. 2:{ exfalso; exact HXE. }
    destruct (Z.eq_dec r6 PARSE_OK) as [->|NE]; [| err1 P1 fb_resp_at constr:(0x10646%Z) X_resp].
    eapply (cont_next q lo S MB A len cap cur0 bs VOK _ 47); [rd_resp| reflexivity| lia| lia|]. open_FX FXH. clear FR0. destruct F0H as [? FR0]. unfold H_vfmatch_A.F0 in FR0. dex.

    dcall (dir_lit q lo S MB A len cap cur0 bs VOK) r7 c7 X7. 2:{ exfalso; exact HXE. }
    destruct (Z.eq_dec r7 PARSE_OK) as [->|NE]; [| err1 P1 fb_resp_at constr:(0x10646%Z) X_resp].
    eapply (cont_next q lo S MB A len cap cur0 bs VOK _ 37); [rd_resp| reflexivity| lia| lia|]. open_FX FXH. clear FR0. destruct F0H as [? FR0]. unfold H_vfmatch_A.F0 in FR0. dex.

    dcall (dir_w q lo S MB A len cap cur0 bs VOK) r8 c8 X8; [rd_resp| reflexivity| |]. 2:{ exfalso; exact HXE. }
    destruct (Z.eq_dec r8 PARSE_OK) as [->|NE]; [| err1 P1 fb_resp_at constr:(0x10646%Z) X_resp].
    eapply (cont_next q lo S MB A len cap cur0 bs VOK _ 37); [rd_resp| reflexivity| lia| lia|]. open_FX FXH. clear FR0. destruct F0H as [? FR0]. unfold H_vfmatch_A.F0 in FR0. dex.

    dcall (dir_L q lo S MB A len cap cur0 bs VOK) r9 c9 X9; [rd_resp| reflexivity| |]. 2:{ exfalso; exact HXE. }
    destruct X9 as (pa & pb & PC1 & -> & HXL).
    destruct (Z.eq_dec r9 PARSE_OK) as [->|NE]; [| err1 P1 fb_resp_at constr:(0x10646%Z) X_resp].
    destruct (HXL eq_refl) as (l & -> & L0 & C9 & C9L & CRB).
    eapply (cont_next q lo S MB A len cap cur0 bs VOK _ 37); [rd_resp| reflexivity| lia| lia|]. open_FX FXH. clear FR0. destruct F0H as [? FR0]. unfold H_vfmatch_A.F0 in FR0. dex.

    dcall (dir_c q lo S MB A len cap cur0 bs VOK) r10 c10 X10; [rd_resp| reflexivity| |]. 2:{ exfalso; exact HXE. }
    destruct (Z.eq_dec r10 PARSE_OK) as [->|NE]; [| err1 P1 fb_resp_at constr:(0x10646%Z) X_resp].
    eapply evt_mono.
    { eapply cont_end with (R := fun mm => rw_cells rsegs mm P1 [C8 (wz (A + c8)); C8 (wz l)])
                            (XP := (fun r c => r = PARSE_OK -> cur0 <= c8 /\ 0 <= l /\ c8 + l < c /\ c <= len)%Z);
      try eassumption; try rd_resp; try reflexivity; try (unfold PARSE_OK in *; lia). }
    intros ms' V; eapply vpost_mono; [| exact V]; cbn beta; intros mm rr cc [HRm HXP].
    unfold X_resp. do 2 eexists; split; [exact HRm|]. intros E. exists c8, l. pose proof (HXP E). use_ok.
    repeat (split; [first [reflexivity| lia]|]). rewrite <- C9. first [exact CRB | eexists; exact CRB].
  Qed.

End VFG.
