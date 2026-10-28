(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_ctype H_scanner_get_token H_vfmatch_A H_vfmatch_B H_vfmatch_F HU_vfm_ws HU_vfm_lit.
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

Definition qm8 (x : Z) : Prop := (x mod 8 = 0)%Z.

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
  Ltac ofx := lazymatch goal with Y : ex (fun _ => H_vfmatch_A.F0 _ _ _ _) |- _ => destruct Y as [? F0T] end;
    lazymatch goal with X : H_vfmatch_A.FX _ _ |- _ => open_FX X end;
    lazymatch goal with H : rw_cells _ _ _ [CB 8 _; C8 _; C8 _; C8 _; CB 4 _] |- _ => clear H end;
    unfold H_vfmatch_A.F0 in *; dex.

  Notation FMT_REQ09 := 0x10331%Z.
  Definition fb_req09 : list byte := map (Z_to_bv 8) [37; 115; 9; 37; 83; 37; 119; 37; 99; 0].
  #[using="Type"] Lemma fb_req09_at : forall m, mem_inv rsegs m -> bytes_at rsegs m FMT_REQ09 fb_req09.
  Proof.
    intros m MI. pose proof (ro_cells_image rsegs m FMT_REQ09 fb_req09 MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO.
    destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
  Qed.
  Ltac rd_req09 := rdfmt fb_req09_at constr:(0x10331%Z).

  Definition X_req09 (P1 P2 : Z) : mem -> Z -> Z -> Prop := fun m' r cur' =>
    (exists pa pb pc pd, rw_cells rsegs m' P1 [C8 pa; C8 pb] /\ rw_cells rsegs m' P2 [C8 pc; C8 pd]
       /\ (r = PARSE_OK -> exists o1 l1 o2 l2, pa = wz (A + o1) /\ pb = wz l1 /\ pc = wz (A + o2) /\ pd = wz l2
             /\ cur0 <= o1 /\ 1 <= l1 /\ o1 + l1 < o2 /\ 1 <= l2 /\ o2 + l2 < len /\ o2 + l2 < cur' /\ cur' <= len))%Z.

  #[using="VOK"] Theorem vf_req09 : forall (P1 P2 : Z) (pw1 pw2 pw3 pw4 : word) ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m,
    stk rsegs m lo q -> mem_inv rsegs m -> SCc m cur0 -> MBc m -> BUFc m ->
    rw_cells rsegs m (q + 16) [C8 (wz P1)] -> rw_cells rsegs m P1 [C8 pw1; C8 pw2] -> (q + 64 <= P1 /\ P1 + 16 <= MB)%Z -> (P1 mod 8 = 0)%Z ->
    rw_cells rsegs m (q + 16 + 8) [C8 (wz P2)] -> rw_cells rsegs m P2 [C8 pw3; C8 pw4] -> (q + 64 <= P2 /\ P2 + 16 <= MB)%Z -> (P2 mod 8 = 0)%Z ->
    (P1 + 16 <= P2 \/ P2 + 16 <= P1)%Z ->
    evt rsegs (vpost ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (WF [(P1, P1 + 16); (P2, P2 + 16)]%Z) (X_req09 P1 P2) m)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz S) (wz FMT_REQ09) (wz (q + 16)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz vfmatch_entry) fc None m (seg_rom rsegs)).
  Proof.
    pose proof VOK as VOK'. vok VOK'. clear Q8 S8 MB8.
    intros until m. intros ST MI SC MBC BUF GC1 PC1 PL1 PA1 GC2 PC2 PL2 PA2 P12. unfx.
    change (qm8 P1) in PA1. change (qm8 P2) in PA2.
    pose proof (munch_refl (WF [(P1, P1 + 16); (P2, P2 + 16)]%Z) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    eapply evt_cut.
    { eapply (prologue q lo S MB A len cap cur0 bs VOK FMT_REQ09 37 (q + 16) (Z_to_bv 8 37)); try eassumption; try reflexivity; try lia. intros m1 MI1. rd_req09. }
    post_call rsegs m. rename PC into ST. rename PC0 into FSH. rename POST into F0H.
    lazymatch goal with H : H_vfmatch_A.FX _ _ |- _ => rename H into FXH end. ofx. unfold FS in FSH.

    dcall (dir_s q lo S MB A len cap cur0 bs VOK) r1 c1 X1; [rd_req09| reflexivity| |]. 2:{ exfalso; exact HXE. }
    destruct X1 as (pa & pb & PC1 & HXs).
    destruct (Z.eq_dec r1 PARSE_OK) as [->|NE]; [| err2 P1 P2 fb_req09_at constr:(0x10331%Z) X_req09].
    destruct (HXs eq_refl) as (l1 & -> & -> & L1 & C1 & C1L).
    eapply (cont_next q lo S MB A len cap cur0 bs VOK _ 9); [rd_req09| reflexivity| lia| lia|]. ofx.

    dcall (dir_tab q lo S MB A len cap cur0 bs VOK) r2 c2 X2. 2:{ exfalso; exact HXE. }
    destruct (Z.eq_dec r2 PARSE_OK) as [->|NE]; [| err2 P1 P2 fb_req09_at constr:(0x10331%Z) X_req09].
    eapply (cont_next q lo S MB A len cap cur0 bs VOK _ 37); [rd_req09| reflexivity| lia| lia|]. ofx.

    dcall (dir_S q lo S MB A len cap cur0 bs VOK) r3 c3 X3; [rd_req09| reflexivity| |]. 2:{ exfalso; exact HXE. }
    unfold XS in X3. destruct X3 as (pc & pd & PC2 & HXS).
    destruct (Z.eq_dec r3 PARSE_OK) as [->|NE]; [| err2 P1 P2 fb_req09_at constr:(0x10331%Z) X_req09].
    destruct (HXS eq_refl) as (l2 & -> & -> & L2 & C3 & C3L).
    eapply (cont_next q lo S MB A len cap cur0 bs VOK _ 37); [rd_req09| reflexivity| lia| lia|]. ofx.

    dcall (dir_w q lo S MB A len cap cur0 bs VOK) r4 c4 X4; [rd_req09| reflexivity| |]. 2:{ exfalso; exact HXE. }
    destruct (Z.eq_dec r4 PARSE_OK) as [->|NE]; [| err2 P1 P2 fb_req09_at constr:(0x10331%Z) X_req09].
    eapply (cont_next q lo S MB A len cap cur0 bs VOK _ 37); [rd_req09| reflexivity| lia| lia|]. ofx.

    dcall (dir_c q lo S MB A len cap cur0 bs VOK) r5 c5 X5; [rd_req09| reflexivity| |]. 2:{ exfalso; exact HXE. }
    destruct (Z.eq_dec r5 PARSE_OK) as [->|NE]; [| err2 P1 P2 fb_req09_at constr:(0x10331%Z) X_req09].
    eapply evt_mono.
    { eapply cont_end with (R := fun mm => rw_cells rsegs mm P1 [C8 (wz (A + cur0)); C8 (wz l1)] /\ rw_cells rsegs mm P2 [C8 (wz (A + c2)); C8 (wz l2)])
                            (XP := (fun r c => r = PARSE_OK -> 1 <= l1 /\ cur0 + l1 < c2 /\ 1 <= l2 /\ c2 + l2 < len /\ c2 + l2 < c /\ c <= len)%Z);
      try eassumption; try rd_req09; try reflexivity; try (use_ok; lia). split; assumption. }
    intros ms' V; eapply vpost_mono; [| exact V]; cbn beta; intros mm rr cc [[HRm1 HRm2] HXP].
    unfold X_req09. do 4 eexists; split; [exact HRm1|]; split; [exact HRm2|]. intros E. exists cur0, l1, c2, l2. pose proof (HXP E). use_ok.
    repeat (split; [first [reflexivity| lia]|]). lia.
  Qed.

  Notation FMT_REQ := 0x10423%Z.
  Definition fb_req : list byte := map (Z_to_bv 8) [37; 115; 9; 37; 83; 9; 37; 105; 104; 116; 116; 112; 37; 119; 47; 37; 119; 37; 76; 37; 99; 0].
  #[using="Type"] Lemma fb_req_at : forall m, mem_inv rsegs m -> bytes_at rsegs m FMT_REQ fb_req.
  Proof.
    intros m MI. pose proof (ro_cells_image rsegs m FMT_REQ fb_req MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO.
    destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
  Qed.
  Ltac rd_req := rdfmt fb_req_at constr:(0x10423%Z).

  Definition X_req (P1 P2 P3 : Z) : mem -> Z -> Z -> Prop := fun m' r cur' =>
    (exists pa pb pc pd pe pf, rw_cells rsegs m' P1 [C8 pa; C8 pb] /\ rw_cells rsegs m' P2 [C8 pc; C8 pd] /\ rw_cells rsegs m' P3 [C8 pe; C8 pf]
       /\ (r = PARSE_OK -> exists o1 l1 o2 l2 o3 l3, pa = wz (A + o1) /\ pb = wz l1 /\ pc = wz (A + o2) /\ pd = wz l2
             /\ pe = wz (A + o3) /\ pf = wz l3
             /\ cur0 <= o1 /\ 1 <= l1 /\ o1 + l1 < o2 /\ 1 <= l2 /\ o2 + l2 < o3 /\ 0 <= l3 /\ o3 + l3 < cur' /\ cur' <= len
             /\ exists b, nth_error bs (Z.to_nat (o3 + l3)) = Some b /\ (bv_unsigned b = 13 \/ bv_unsigned b = 10)))%Z.

  #[using="VOK"] Theorem vf_req : forall (P1 P2 P3 : Z) (pw1 pw2 pw3 pw4 pw5 pw6 : word) ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m,
    stk rsegs m lo q -> mem_inv rsegs m -> SCc m cur0 -> MBc m -> BUFc m ->
    rw_cells rsegs m (q + 16) [C8 (wz P1)] -> rw_cells rsegs m P1 [C8 pw1; C8 pw2] -> (q + 64 <= P1 /\ P1 + 16 <= MB)%Z -> (P1 mod 8 = 0)%Z ->
    rw_cells rsegs m (q + 16 + 8) [C8 (wz P2)] -> rw_cells rsegs m P2 [C8 pw3; C8 pw4] -> (q + 64 <= P2 /\ P2 + 16 <= MB)%Z -> (P2 mod 8 = 0)%Z ->
    rw_cells rsegs m (q + 16 + 8 + 8) [C8 (wz P3)] -> rw_cells rsegs m P3 [C8 pw5; C8 pw6] -> (q + 64 <= P3 /\ P3 + 16 <= MB)%Z -> (P3 mod 8 = 0)%Z ->
    (P1 + 16 <= P2 \/ P2 + 16 <= P1)%Z -> (P1 + 16 <= P3 \/ P3 + 16 <= P1)%Z -> (P2 + 16 <= P3 \/ P3 + 16 <= P2)%Z ->
    evt rsegs (vpost ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (WF [(P1, P1 + 16); (P2, P2 + 16); (P3, P3 + 16)]%Z) (X_req P1 P2 P3) m)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz S) (wz FMT_REQ) (wz (q + 16)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz vfmatch_entry) fc None m (seg_rom rsegs)).
  Proof.
    pose proof VOK as VOK'. vok VOK'. clear Q8 S8 MB8.
    intros until m. intros ST MI SC MBC BUF GC1 PC1 PL1 PA1 GC2 PC2 PL2 PA2 GC3 PC3 PL3 PA3 P12 P13 P23. unfx.
    change (qm8 P1) in PA1. change (qm8 P2) in PA2. change (qm8 P3) in PA3.
    pose proof (munch_refl (WF [(P1, P1 + 16); (P2, P2 + 16); (P3, P3 + 16)]%Z) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    eapply evt_cut.
    { eapply (prologue q lo S MB A len cap cur0 bs VOK FMT_REQ 37 (q + 16) (Z_to_bv 8 37)); try eassumption; try reflexivity; try lia. intros m1 MI1. rd_req. }
    post_call rsegs m. rename PC into ST. rename PC0 into FSH. rename POST into F0H.
    lazymatch goal with H : H_vfmatch_A.FX _ _ |- _ => rename H into FXH end. ofx. unfold FS in FSH.

    dcall (dir_s q lo S MB A len cap cur0 bs VOK) r1 c1 X1; [rd_req| reflexivity| |]. 2:{ exfalso; exact HXE. }
    destruct X1 as (pa & pb & PC1 & HXs).
    destruct (Z.eq_dec r1 PARSE_OK) as [->|NE]; [| err3 P1 P2 P3 fb_req_at constr:(0x10423%Z) X_req].
    destruct (HXs eq_refl) as (l1 & -> & -> & L1 & C1 & C1L).
    eapply (cont_next q lo S MB A len cap cur0 bs VOK _ 9); [rd_req| reflexivity| lia| lia|]. ofx.

    dcall (dir_tab q lo S MB A len cap cur0 bs VOK) r2 c2 X2. 2:{ exfalso; exact HXE. }
    destruct (Z.eq_dec r2 PARSE_OK) as [->|NE]; [| err3 P1 P2 P3 fb_req_at constr:(0x10423%Z) X_req].
    eapply (cont_next q lo S MB A len cap cur0 bs VOK _ 37); [rd_req| reflexivity| lia| lia|]. ofx.

    dcall (dir_S q lo S MB A len cap cur0 bs VOK) r3 c3 X3; [rd_req| reflexivity| |]. 2:{ exfalso; exact HXE. }
    unfold XS in X3. destruct X3 as (pc & pd & PC2 & HXS).
    destruct (Z.eq_dec r3 PARSE_OK) as [->|NE]; [| err3 P1 P2 P3 fb_req_at constr:(0x10423%Z) X_req].
    destruct (HXS eq_refl) as (l2 & -> & -> & L2 & C3 & C3L).
    eapply (cont_next q lo S MB A len cap cur0 bs VOK _ 9); [rd_req| reflexivity| lia| lia|]. ofx.

    dcall (dir_tab q lo S MB A len cap cur0 bs VOK) r4 c4 X4. 2:{ exfalso; exact HXE. }
    destruct (Z.eq_dec r4 PARSE_OK) as [->|NE]; [| err3 P1 P2 P3 fb_req_at constr:(0x10423%Z) X_req].
    eapply (cont_next q lo S MB A len cap cur0 bs VOK _ 37); [rd_req| reflexivity| lia| lia|]. ofx.

    dcall (dir_i q lo S MB A len cap cur0 bs VOK) r5 c5 X5; [rd_req| reflexivity| |]. 2:{ exfalso; exact HXE. }
    destruct X5 as [-> ->].
    eapply (cont_next q lo S MB A len cap cur0 bs VOK _ 104); [rd_req| reflexivity| lia| lia|]. ofx.

    dcall (dir_lit q lo S MB A len cap cur0 bs VOK) r6 c6 X6. 2:{ first [exfalso; exact HXE | err3 P1 P2 P3 fb_req_at constr:(0x10423%Z) X_req]. }
    destruct (Z.eq_dec r6 PARSE_OK) as [->|NE]; [| err3 P1 P2 P3 fb_req_at constr:(0x10423%Z) X_req].
    eapply (cont_next q lo S MB A len cap cur0 bs VOK _ 116); [rd_req| reflexivity| lia| lia|]. ofx.
    dcall (dir_lit q lo S MB A len cap cur0 bs VOK) r7 c7 X7. 2:{ first [exfalso; exact HXE | err3 P1 P2 P3 fb_req_at constr:(0x10423%Z) X_req]. }
    destruct (Z.eq_dec r7 PARSE_OK) as [->|NE]; [| err3 P1 P2 P3 fb_req_at constr:(0x10423%Z) X_req].
    eapply (cont_next q lo S MB A len cap cur0 bs VOK _ 116); [rd_req| reflexivity| lia| lia|]. ofx.
    dcall (dir_lit q lo S MB A len cap cur0 bs VOK) r8 c8 X8. 2:{ first [exfalso; exact HXE | err3 P1 P2 P3 fb_req_at constr:(0x10423%Z) X_req]. }
    destruct (Z.eq_dec r8 PARSE_OK) as [->|NE]; [| err3 P1 P2 P3 fb_req_at constr:(0x10423%Z) X_req].
    eapply (cont_next q lo S MB A len cap cur0 bs VOK _ 112); [rd_req| reflexivity| lia| lia|]. ofx.
    dcall (dir_lit q lo S MB A len cap cur0 bs VOK) r9 c9 X9. 2:{ first [exfalso; exact HXE | err3 P1 P2 P3 fb_req_at constr:(0x10423%Z) X_req]. }
    destruct (Z.eq_dec r9 PARSE_OK) as [->|NE]; [| err3 P1 P2 P3 fb_req_at constr:(0x10423%Z) X_req].
    eapply (cont_next q lo S MB A len cap cur0 bs VOK _ 37); [rd_req| reflexivity| lia| lia|]. ofx.

    dcall (dir_w q lo S MB A len cap cur0 bs VOK) r10 c10 X10; [rd_req| reflexivity| |]. 2:{ exfalso; exact HXE. }
    destruct (Z.eq_dec r10 PARSE_OK) as [->|NE]; [| err3 P1 P2 P3 fb_req_at constr:(0x10423%Z) X_req].
    eapply (cont_next q lo S MB A len cap cur0 bs VOK _ 47); [rd_req| reflexivity| lia| lia|]. ofx.

    dcall (dir_lit q lo S MB A len cap cur0 bs VOK) r11 c11 X11. 2:{ first [exfalso; exact HXE | err3 P1 P2 P3 fb_req_at constr:(0x10423%Z) X_req]. }
    destruct (Z.eq_dec r11 PARSE_OK) as [->|NE]; [| err3 P1 P2 P3 fb_req_at constr:(0x10423%Z) X_req].
    eapply (cont_next q lo S MB A len cap cur0 bs VOK _ 37); [rd_req| reflexivity| lia| lia|]. ofx.

    dcall (dir_w q lo S MB A len cap cur0 bs VOK) r12 c12 X12; [rd_req| reflexivity| |]. 2:{ exfalso; exact HXE. }
    destruct (Z.eq_dec r12 PARSE_OK) as [->|NE]; [| err3 P1 P2 P3 fb_req_at constr:(0x10423%Z) X_req].
    eapply (cont_next q lo S MB A len cap cur0 bs VOK _ 37); [rd_req| reflexivity| lia| lia|]. ofx.

    dcall (dir_L q lo S MB A len cap cur0 bs VOK) r13 c13 X13; [rd_req| reflexivity| |]. 2:{ exfalso; exact HXE. }
    destruct X13 as (pe & pf & PC3 & -> & HXL).
    destruct (Z.eq_dec r13 PARSE_OK) as [->|NE]; [| err3 P1 P2 P3 fb_req_at constr:(0x10423%Z) X_req].
    destruct (HXL eq_refl) as (l3 & -> & L3 & C13 & C13L & CRB).
    eapply (cont_next q lo S MB A len cap cur0 bs VOK _ 37); [rd_req| reflexivity| lia| lia|]. ofx.

    dcall (dir_c q lo S MB A len cap cur0 bs VOK) r14 c14 X14; [rd_req| reflexivity| |]. 2:{ exfalso; exact HXE. }
    destruct (Z.eq_dec r14 PARSE_OK) as [->|NE]; [| err3 P1 P2 P3 fb_req_at constr:(0x10423%Z) X_req].
    eapply evt_mono.
    { eapply cont_end with (R := fun mm => rw_cells rsegs mm P1 [C8 (wz (A + cur0)); C8 (wz l1)] /\ rw_cells rsegs mm P2 [C8 (wz (A + c2)); C8 (wz l2)]
                                        /\ rw_cells rsegs mm P3 [C8 (wz (A + c12)); C8 (wz l3)])
                            (XP := (fun r c => r = PARSE_OK -> 1 <= l1 /\ cur0 + l1 < c2 /\ 1 <= l2 /\ c2 + l2 < c12 /\ 0 <= l3 /\ c12 + l3 < c /\ c <= len)%Z);
      try eassumption; try rd_req; try reflexivity; try (use_ok; lia). split; [assumption| split; assumption]. }
    intros ms' V; eapply vpost_mono; [| exact V]; cbn beta; intros mm rr cc [[HRm1 [HRm2 HRm3]] HXP].
    unfold X_req. do 6 eexists; split; [exact HRm1|]; split; [exact HRm2|]; split; [exact HRm3|]. intros E.
    exists cur0, l1, c2, l2, c12, l3. pose proof (HXP E). use_ok.
    repeat (split; [first [reflexivity| lia]|]). rewrite <- C13. first [exact CRB | eexists; exact CRB].
  Qed.
End VFG.
