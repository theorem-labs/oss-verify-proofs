(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Bytes Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsImgSh AsIface AsIface5 AsIface6 AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AsTRList.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import X8Kit X8SRKit XL_mutex X8_asio_stmt_alloc X8_asio_stmt_sp X8_asio_stmt_sp2.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record svce := mkSE { se_addr : Z ; se_hdr : svch ; se_tiname : Z }.

Definition svch_ok (S : svch) : Prop :=
  0 <= sv_vptr S < 2^64 /\ 0 <= sv_ti S < 2^64 /\ 0 <= sv_id S < 2^64 /\ 0 <= sv_owner S < 2^64
  /\ 0 <= sv_next S < 2^64 /\ 0 <= sv_destroy S < 2^64.

(* [comment removed for export] *)
Definition keys_match (kti kid kname : Z) (e : svce) : bool :=
  (negb (sv_id (se_hdr e) =? 0) && (sv_id (se_hdr e) =? kid))
  || (negb (sv_ti (se_hdr e) =? 0) && negb (kti =? 0) && (se_tiname e =? kname)).

(* [comment removed for export] *)
Fixpoint find_svc (kti kid kname : Z) (L : list svce) : Z :=
  match L with
  | [] => 0
  | e :: L' => if keys_match kti kid kname e then se_addr e else find_svc kti kid kname L'
  end.

Lemma keys_match_false_inv : forall kti kid kname e,
  keys_match kti kid kname e = false ->
  (sv_id (se_hdr e) = 0 \/ sv_id (se_hdr e) <> kid)
  /\ (sv_ti (se_hdr e) = 0 \/ kti = 0 \/ se_tiname e <> kname).
Proof.
  intros kti kid kname e H. unfold keys_match in H.
  apply orb_false_iff in H. destruct H as [H1 H2].
  apply andb_false_iff in H1. apply andb_false_iff in H2.
  split.
  - destruct H1 as [H1|H1].
    + left. apply negb_false_iff in H1. apply Z.eqb_eq in H1. exact H1.
    + right. apply Z.eqb_neq in H1. exact H1.
  - destruct H2 as [H2|H2].
    + apply andb_false_iff in H2. destruct H2 as [H2|H2]; apply negb_false_iff in H2; apply Z.eqb_eq in H2; lia.
    + right; right. apply Z.eqb_neq in H2. exact H2.
Qed.

Lemma keys_match_true_id : forall kti kid kname a S nm,
  sv_id S <> 0 -> sv_id S = kid -> keys_match kti kid kname (mkSE a S nm) = true.
Proof.
  intros. unfold keys_match; cbn [se_hdr se_tiname]. apply orb_true_iff. left. apply andb_true_iff. split.
  - apply negb_true_iff. apply Z.eqb_neq. assumption.
  - apply Z.eqb_eq. assumption.
Qed.
Lemma keys_match_true_ti : forall kti kid kname a S nm,
  sv_ti S <> 0 -> kti <> 0 -> nm = kname -> keys_match kti kid kname (mkSE a S nm) = true.
Proof.
  intros. unfold keys_match; cbn [se_hdr se_tiname]. apply orb_true_iff. right. repeat (apply andb_true_iff; split).
  - apply negb_true_iff. apply Z.eqb_neq. assumption.
  - apply negb_true_iff. apply Z.eqb_neq. assumption.
  - apply Z.eqb_eq. assumption.
Qed.
Lemma keys_match_false_intro : forall kti kid kname a S nm,
  (sv_id S = 0 \/ sv_id S <> kid) -> (sv_ti S = 0 \/ kti = 0 \/ nm <> kname) ->
  keys_match kti kid kname (mkSE a S nm) = false.
Proof.
  intros kti kid kname a S nm H1 H2. unfold keys_match; cbn [se_hdr se_tiname]. apply orb_false_iff. split.
  - apply andb_false_iff. destruct H1 as [H1|H1]; [left; apply negb_false_iff; apply Z.eqb_eq; exact H1| right; apply Z.eqb_neq; exact H1].
  - apply andb_false_iff. destruct H2 as [H2|[H2|H2]].
    + left. apply andb_false_iff. left. apply negb_false_iff. apply Z.eqb_eq. exact H2.
    + left. apply andb_false_iff. right. apply negb_false_iff. apply Z.eqb_eq. exact H2.
    + right. apply Z.eqb_neq. exact H2.
Qed.
Lemma find_svc_none : forall kti kid kname L,
  Forall (fun e => keys_match kti kid kname e = false) L -> find_svc kti kid kname L = 0.
Proof. induction L as [|e L IH]; intros F; [reflexivity|]. cbn. rewrite (Forall_inv F). apply IH. exact (Forall_inv_tail F). Qed.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Definition ati_ok (m : mem) (ti nm : Z) : Prop :=
  ro_cells asegs m (ti + 8) [C8 (wz nm)] /\ 0 <= nm < 2^64
  /\ 0x115000 <= ti /\ ti + 16 <= 0x125e40 /\ ti mod 8 = 0 /\ aimg0b (ti + 8) 8 = true.

Definition asvce_ok (m : mem) (e : svce) : Prop :=
  0 < se_addr e /\ se_addr e mod 8 = 0 /\ aapp (se_addr e) 48
  /\ ro_cells asegs m (se_addr e) (SvcHdrCells (se_hdr e)) /\ svch_ok (se_hdr e)
  /\ accessible m (se_addr e) 48
  /\ (sv_ti (se_hdr e) <> 0 -> ati_ok m (sv_ti (se_hdr e)) (se_tiname e)).

Fixpoint ASvcChain (m : mem) (first : Z) (L : list svce) : Prop :=
  match L with
  | [] => first = 0
  | e :: L' => first = se_addr e /\ asvce_ok m e /\ ASvcChain m (sv_next (se_hdr e)) L'
  end.

Lemma ASvcChain_nil_inv : forall m first, ASvcChain m first [] -> first = 0.
Proof. intros m first H. exact H. Qed.
Lemma ASvcChain_head : forall m first L, ASvcChain m first L -> L <> [] -> 0 < first /\ first + 48 <= aceil /\ first mod 8 = 0.
Proof.
  intros m first [|e L] CH NE; [congruence|]. cbn in CH. destruct CH as (-> & (POS & A8 & AP & _) & _).
  pose proof (aapp_bounds _ _ AP ltac:(lia)) as (B1 & B2 & B3 & B4 & B5). lia.
Qed.
Lemma ASvcChain_zero : forall m L, ASvcChain m 0 L -> L = [].
Proof. intros m [|e L] CH; [reflexivity|]. cbn in CH. destruct CH as (E & (POS & _) & _). lia. Qed.

(* [comment removed for export] *)
Lemma ati_ok_transport : forall W m m' ti nm,
  ati_ok m ti nm -> munch W m m' -> Forall (fun iv : Z * Z => 0x125e40 <= fst iv \/ snd iv <= 0x115000) W -> ati_ok m' ti nm.
Proof.
  intros W m m' ti nm (RO & R & LO' & HI' & T8 & IMG) MU FW. split; [| split; [exact R| split; [exact LO'| split; [exact HI'| split; [exact T8| exact IMG]]]]].
  eapply ro_cells_transport; [exact RO| exact MU|]. cbn [cells_size csize Nat.add].
  clear - FW LO' HI'. induction W as [|[lo hi] W IH]; [exact I|].
  pose proof (Forall_inv FW) as H1. cbn in H1. cbn. split; [lia|]. apply IH. exact (Forall_inv_tail FW).
Qed.

(* [comment removed for export] *)
Lemma ASvcChain_transport_fr : forall W m m' ff k first L,
  ASvcChain m first L -> munch W m m' ->
  Forall (win_fr ff k) W -> 0 <= ff -> ff mod 8 = 0 -> 0 <= k ->
  Forall (fun iv : Z * Z => 0x125e40 <= fst iv \/ snd iv <= 0x115000) W ->
  Forall (fun e => disjoint_from W (se_addr e) 48 /\ (se_addr e + 48 <= ff \/ ff + 8 * k <= se_addr e)) L ->
  ASvcChain m' first L.
Proof.
  intros W m m' ff k first L. revert first. induction L as [|e L IH]; intros first CH MU FW F0 F8 K0 FI OFF; [exact CH|].
  cbn in CH |- *. destruct CH as (E & (POS & A8 & AP & HD & OK & AC & TI) & CH').
  pose proof (Forall_inv OFF) as [O1 O2].
  split; [exact E|]. split.
  - split; [exact POS|]. split; [exact A8|]. split; [exact AP|].
    split. { eapply ro_cells_transport; [exact HD| exact MU|]. cbn [cells_size csize Nat.add SvcHdrCells]. exact O1. }
    split; [exact OK|].
    split. { eapply accessible_transport_fr; [exact AC| exact MU| exact FW| exact F0| exact F8| exact K0| exact O2]. }
    intros NZ. eapply ati_ok_transport; [exact (TI NZ)| exact MU| exact FI].
  - apply IH; [exact CH'| exact MU| exact FW| exact F0| exact F8| exact K0| exact FI| exact (Forall_inv_tail OFF)].
Qed.

Lemma ASvcChain_Forall : forall m first L, ASvcChain m first L -> Forall (asvce_ok m) L.
Proof.
  intros m first L. revert first. induction L as [|e L IH]; intros first CH; [constructor|].
  cbn in CH. destruct CH as (_ & OK & CH'). constructor; [exact OK| exact (IH _ CH')].
Qed.

(* [comment removed for export] *)
Lemma ati_ok_transport_hi : forall W m m' ti nm, ati_ok m ti nm -> munch W m m' -> wins_hi W -> ati_ok m' ti nm.
Proof.
  intros W m m' ti nm TI MU WH. eapply ati_ok_transport; [exact TI| exact MU|].
  eapply Forall_impl; [| exact WH]. intros [l h] K. cbn [fst snd] in *. unfold AIMG_TOP, AHI_LO in K. lia.
Qed.
Lemma ASvcChain_transport_hi : forall W m m' first L,
  ASvcChain m first L -> munch W m m' -> wins_hi W -> Forall (fun e => disjoint_from W (se_addr e) 48) L ->
  ASvcChain m' first L.
Proof.
  intros W m m' first L CH MU WH OFF.
  eapply (ASvcChain_transport_fr W m m' 0 0); [exact CH| exact MU| | lia| reflexivity| lia| |].
  - eapply Forall_impl; [| exact WH]. intros [l h] K. unfold win_fr. cbn [fst snd] in *. lia.
  - eapply Forall_impl; [| exact WH]. intros [l h] K. cbn [fst snd] in *. unfold AIMG_TOP, AHI_LO in K. lia.
  - pose proof (ASvcChain_Forall _ _ _ CH) as FO. clear CH MU WH. induction L as [|e L IH]; [constructor|].
    pose proof (Forall_inv FO) as (POS & _). constructor; [split; [exact (Forall_inv OFF)| right; lia]|].
    apply IH; [exact (Forall_inv_tail OFF)| exact (Forall_inv_tail FO)].
Qed.

(* [comment removed for export] *)
Lemma ASvcChain_off3 : forall m first L lo h r svc,
  ASvcChain m first L -> aceil <= lo ->
  Forall (fun e => (se_addr e + 48 <= r \/ r + SZ_REG <= se_addr e) /\ (se_addr e + 48 <= svc \/ svc + SZ_SVC <= se_addr e)) L ->
  Forall (fun e => disjoint_from [(lo, h); (r, r + SZ_REG); (svc, svc + SZ_SVC)]%Z (se_addr e) 48) L.
Proof.
  intros m first L lo h r svc CH CE OFF. pose proof (ASvcChain_Forall _ _ _ CH) as FO. clear CH.
  induction L as [|e L IH]; [constructor|].
  pose proof (Forall_inv FO) as (POS & _ & AP & _). pose proof (Forall_inv OFF) as (O1 & O2).
  pose proof (aapp_bounds _ _ AP ltac:(lia)) as (B1 & B2 & B3 & B4 & B5).
  constructor; [| apply IH; [exact (Forall_inv_tail OFF)| exact (Forall_inv_tail FO)]].
  cbn [disjoint_from fst snd]. split; [left; lia|]. split; [lia|]. split; [lia| exact I].
Qed.

Section W.
  Variable H : asr.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ADAS_STACK : Z := 144 + AINTRIN_STACK.

Definition das_W (lo : Z) (sp : word) (r svc ff fp : Z) : list (Z * Z) :=
  [(lo, bv_unsigned sp); (r, r + SZ_REG); (svc, svc + SZ_SVC);
   (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 128); (sh ff, sh ff + 16)]%Z.

Definition do_add_service_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (LB : list block) (LF : list fframe) (r svc owner first kti kid lo shi : Z) (S0 : svch) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (ff fp : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (das_W lo sp r svc ff fp) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ ARegistry LB m' r owner svc 0
    /\ rw_cells asegs m' svc (SvcHdrCells (mkSVC (sv_vptr S0) kti kid owner first (sv_destroy S0)))
    /\ fresh_frame H LF 1 ff fp /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi.

Definition do_add_service_stmt : Prop :=
  forall (r K svc lo shi : Z) (LB : list block) (LF : list fframe) (L : list svce) (S0 : svch) (owner first kti kid kname : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  ARegistry LB m r owner first 0 ->
  rw_cells asegs m svc (SvcHdrCells S0) -> svch_ok S0 -> sv_owner S0 = owner -> sv_destroy S0 <> 0 ->
  ro_cells asegs m K [C8 (wz kti); C8 (wz kid)] -> 0 <= kti < 2^64 -> 0 <= kid < 2^64 -> 0 <= kname < 2^64 ->
  (kti <> 0 -> ati_ok m kti kname) ->
  ASvcChain m first L -> Forall (fun e => keys_match kti kid kname e = false) L ->
  Forall (fun e => fsobj H LF (se_addr e) 48 /\ (se_addr e + 48 <= r \/ r + SZ_REG <= se_addr e)
                   /\ (se_addr e + 48 <= svc \/ svc + SZ_SVC <= se_addr e)) L ->
  bv_unsigned sp <= K -> K + 80 <= shi -> K mod 8 = 0 ->
  (r + NEWSZ_REG <= svc \/ svc + SZ_SVC <= r) ->
  stk asegs m lo (bv_unsigned sp) -> lo + ADAS_STACK <= bv_unsigned sp -> aceil <= lo ->
  bv_unsigned ra mod 2 = 0 ->
  mem_inv asegs m ->
  (* [comment removed for export] *)
  bv_unsigned sp mod 16 = 0 -> tp = Z_to_bv 64 ATP -> ACONST m -> athr_cells m ->
  as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat ->
  stack0 m lo shi -> bv_unsigned sp + 64 <= shi ->
  fsobj H LF r NEWSZ_REG ->
  aapp svc SZ_SVC -> fsobj H LF svc SZ_SVC -> accessible m svc SZ_SVC -> shvis m svc (svc + SZ_SVC) -> svc mod 8 = 0 ->
  evt asegs (do_add_service_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB LF r svc owner first kti kid lo shi S0 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz r) (wz K) (wz svc) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_A_DO_ADD_SERVICE) fc None m (seg_rom asegs)).

End W.
End HCW.
