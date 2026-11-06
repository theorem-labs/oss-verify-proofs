From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
Require Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcPorts RcPortsLib RcBox RcSynth RcLay
  RcLayLib RcFin RcEmit RcEmitLib ctrl_emit_as_c reac_box_model_upstream_width_c reac_ctrl_build_as_c.
Local Ltac lia ::= em_lia.
Import ListNotations.
Open Scope Z_scope.

Ltac fixret :=
  repeat match goal with
  | |- context [ret_pc (Z_to_bv 64 ?n)] =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.

(* The rows 3 .. 9 of CTRL_FRAMES, by block b. *)

Lemma ba_cases : forall b, 0 <= b <= 6 -> b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6.
Proof. intros b Hb. lia. Qed.

Lemma ba_facts : forall b, 0 <= b <= 6 ->
  ly_k (ba_fr (ba_row b)) = ba_row b /\ 3 <= ba_row b <= 9 /\ ly_bb (ba_row b) = b /\
  ubat (ba_fr (ba_row b)) 20 = (if b <=? 1 then 1 else 0) /\ ubat (ba_fr (ba_row b)) 21 <= 1 /\
  ubat (ba_fr (ba_row b)) 22 <= 1 /\ ubat (ba_fr (ba_row b)) 23 <= 1 /\
  ubat (ba_fr (ba_row b)) 18 = 0 /\ ubat (ba_fr (ba_row b)) 19 = 0 /\
  ly_ao (ba_fr (ba_row b)) = 0 /\ ly_al (ba_fr (ba_row b)) = 0.
Proof.
  intros b Hb. destruct (ba_cases b Hb) as [->|[->|[->|[->|[->|[->| -> ]]]]]];
    repeat split; vm_compute; first [reflexivity | intros ?; discriminate].
Qed.

Lemma ba_fr_len : forall r, length (ba_fr r) = 24%nat.
Proof. reflexivity. Qed.

Lemma ba_E_eq : forall b n mb, 0 <= b <= 6 ->
  em_E (ubat (ba_fr (ba_row b)) 21) (ubat (ba_fr (ba_row b)) 22) n (em_hid mb) = ba_E n mb b.
Proof.
  intros b n mb Hb. unfold em_E, ba_E.
  destruct (ba_cases b Hb) as [->|[->|[->|[->|[->|[->| -> ]]]]]];
    destruct (em_wok n); destruct (em_hid mb =? 0); vm_compute; reflexivity.
Qed.

Lemma ba_len_eq : forall b n, 0 <= b <= 6 -> em_len (ubat (ba_fr (ba_row b)) 21) n = 52 + 36 * n.
Proof.
  intros b n Hb. unfold em_len. destruct (ba_facts b Hb) as (_ & _ & _ & _ & L & _).
  rewrite (proj2 (Z.eqb_neq _ 2)) by lia. reflexivity.
Qed.

Lemma ba_lay : forall k tb zb ao al gb, 3 <= k -> ly_lay k tb zb 0 ao al gb = zb.
Proof.
  intros k tb zb ao al gb Hk. unfold ly_lay, ly_base.
  destruct (Z.eqb_spec k 0); [lia|]. destruct (Z.eqb_spec k 1); [lia|]. destruct (Z.eqb_spec k 2); [lia|].
  reflexivity.
Qed.

Lemma ba_fin1 : forall bs, fin 1 0 0 bs = stamp32 bs.
Proof. reflexivity. Qed.

Lemma ba_fin0 : forall bs, fin 0 0 0 bs = bs.
Proof. reflexivity. Qed.

Lemma ba_sub : forall segs m A bs (k : nat) A' bs', bytes_at segs m A bs -> (k + 24 <= length bs)%nat ->
  A' = A + Z.of_nat k -> bs' = firstn 24 (skipn k bs) -> bytes_at segs m A' bs'.
Proof. intros segs m A bs k A' bs' H Hk -> ->. apply ly_bytes_sub; assumption. Qed.

Lemma ba_row_at : forall segs m b, bytes_at segs m (BA_FR + 72) ba_tbl -> 0 <= b <= 6 ->
  bytes_at segs m (BA_FR + 24 * ba_row b) (ba_fr (ba_row b)).
Proof.
  intros segs m b H Hb.
  apply (ba_sub segs m _ _ (Z.to_nat (24 * (ba_row b - 3))) _ _ H).
  all: destruct (ba_cases b Hb) as [->|[->|[->|[->|[->|[->| -> ]]]]]].
  all: first [ apply Nat.leb_le; vm_compute; reflexivity | vm_compute; reflexivity ].
Qed.

Lemma ba_go_false : forall o md b, o = 0 \/ md = 0 \/ 6 < b -> ba_go o md b = false.
Proof.
  intros o md b H. unfold ba_go.
  destruct (Z.eqb_spec o 0); destruct (Z.eqb_spec md 0); destruct (Z.leb_spec b 6); cbn [negb andb];
    first [reflexivity | exfalso; lia].
Qed.

Lemma ba_go_true : forall o md b, o <> 0 -> md <> 0 -> b <= 6 -> ba_go o md b = true.
Proof.
  intros o md b H1 H2 H3. unfold ba_go.
  rewrite (proj2 (Z.eqb_neq o 0) H1), (proj2 (Z.eqb_neq md 0) H2), (proj2 (Z.leb_le b 6) H3). reflexivity.
Qed.

(* ctrl_emit_as's result for the row of block b, in this contract's terms. *)
Lemma ba_res : forall segs (m' : word -> option byte) o b md n c16 (mb nb tb gb db sb : list byte),
  0 <= b <= 6 ->
  bytes_at segs m' o
    (em_fr db sb c16 (nth 0 (ba_fr (ba_row b)) (Z_to_bv 8 0)) (nth 1 (ba_fr (ba_row b)) (Z_to_bv 8 0))
       (fin (ubat (ba_fr (ba_row b)) 20) (ubat (ba_fr (ba_row b)) 18) (ubat (ba_fr (ba_row b)) 19)
          (ly_lay (ly_k (ba_fr (ba_row b))) tb (ly_Z md mb nb (ly_bb (ly_k (ba_fr (ba_row b))))) 0
             (ly_ao (ba_fr (ba_row b))) (ly_al (ba_fr (ba_row b))) gb))
       (em_len (ubat (ba_fr (ba_row b)) 21) n)) ->
  (ubat (ba_fr (ba_row b)) 21 <> 2 -> em_wok n = true) ->
  (ubat (ba_fr (ba_row b)) 20 = 1 \/ ubat (ba_fr (ba_row b)) 20 = 2 ->
     closes (ubat (ba_fr (ba_row b)) 20) (ubat (ba_fr (ba_row b)) 18) (ubat (ba_fr (ba_row b)) 19)
       (fin (ubat (ba_fr (ba_row b)) 20) (ubat (ba_fr (ba_row b)) 18) (ubat (ba_fr (ba_row b)) 19)
          (ly_lay (ly_k (ba_fr (ba_row b))) tb (ly_Z md mb nb (ly_bb (ly_k (ba_fr (ba_row b))))) 0
             (ly_ao (ba_fr (ba_row b))) (ly_al (ba_fr (ba_row b))) gb)) /\
     (closes (ubat (ba_fr (ba_row b)) 20) (ubat (ba_fr (ba_row b)) 18) (ubat (ba_fr (ba_row b)) 19)
        (ly_lay (ly_k (ba_fr (ba_row b))) tb (ly_Z md mb nb (ly_bb (ly_k (ba_fr (ba_row b))))) 0
           (ly_ao (ba_fr (ba_row b))) (ly_al (ba_fr (ba_row b))) gb) ->
      fin (ubat (ba_fr (ba_row b)) 20) (ubat (ba_fr (ba_row b)) 18) (ubat (ba_fr (ba_row b)) 19)
        (ly_lay (ly_k (ba_fr (ba_row b))) tb (ly_Z md mb nb (ly_bb (ly_k (ba_fr (ba_row b))))) 0
           (ly_ao (ba_fr (ba_row b))) (ly_al (ba_fr (ba_row b))) gb) =
      ly_lay (ly_k (ba_fr (ba_row b))) tb (ly_Z md mb nb (ly_bb (ly_k (ba_fr (ba_row b))))) 0
        (ly_ao (ba_fr (ba_row b))) (ly_al (ba_fr (ba_row b))) gb)) ->
  bytes_at segs m' o (em_fr db sb c16 (Z_to_bv 8 205) (Z_to_bv 8 234) (ba_X md mb nb b) (52 + 36 * n)) /\
  em_wok n = true /\ (b <= 1 -> blocksum (ba_X md mb nb b) = 0) /\
  (blocksum (ly_Z md mb nb b) = 0 -> ba_X md mb nb b = ly_Z md mb nb b).
Proof.
  intros segs m' o b md n c16 mb nb tb gb db sb Hb HB HW HC.
  destruct (ba_facts b Hb) as (FK & KR & FBB & FC & FL & _ & _ & F18 & F19 & FAO & FAL).
  rewrite (ba_len_eq b n Hb) in HB.
  rewrite FK, FBB, FAO, FAL, F18, F19, (ba_lay (ba_row b) tb (ly_Z md mb nb b) 0 0 gb (proj1 KR)) in HB, HC.
  change (nth 0 (ba_fr (ba_row b)) (Z_to_bv 8 0)) with (Z_to_bv 8 205) in HB.
  change (nth 1 (ba_fr (ba_row b)) (Z_to_bv 8 0)) with (Z_to_bv 8 234) in HB.
  assert (W : em_wok n = true) by (apply HW; lia).
  rewrite FC in HB, HC. unfold ba_X. revert HB HC.
  destruct (Z.leb_spec b 1) as [B1|B1]; intros HB HC; cbv iota in HB, HC |- *.
  - rewrite ba_fin1 in HB, HC.
    destruct (HC (or_introl eq_refl)) as [CL IMP]. unfold closes in CL, IMP. destruct CL as [CL _].
    split; [exact HB|]. split; [exact W|]. split; [intros _; exact CL|].
    intros H0. apply IMP. split; [exact H0 | intros H2; discriminate H2].
  - rewrite ba_fin0 in HB.
    split; [exact HB|]. split; [exact W|]. split; [intros H; lia | intros _; reflexivity].
Qed.

Section Build.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a5 a6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (o md b d s ns : Z) (mb nb db sb junk : list byte).

  Local Abbreviation SP0 := (bv_unsigned sp).
  Local Abbreviation LO := (bv_unsigned sp - 352).
  Local Abbreviation NN := (bm_uw md (firstn 8 (skipn 16 mb))).
  Local Abbreviation LEN := (52 + 36 * bm_uw md (firstn 8 (skipn 16 mb))).
  Local Abbreviation GO := (ba_go o md b).
  Local Abbreviation EE := (ba_E (bm_uw md (firstn 8 (skipn 16 mb))) mb b).
  Local Abbreviation NM := ((b = 5 \/ b = 6) /\ has mb <> 0 /\ rname mb <> 0).
  Local Abbreviation RR := (if ba_go o md b && ba_E (bm_uw md (firstn 8 (skipn 16 mb))) mb b
                            then 52 + 36 * bm_uw md (firstn 8 (skipn 16 mb)) else 0).

  Hypothesis HEA : ctrl_emit_as_contract.
  Hypothesis HUW : reac_box_model_upstream_width_contract.
  Hypothesis Ho : 0 <= o < 2^64.
  Hypothesis Hmd : 0 <= md < 2^64.
  Hypothesis Hb : 0 <= b < 2^64.
  Hypothesis Hns : -2^31 <= ns <= 0.
  Hypothesis HS16 : SP0 mod 16 = 0.
  Hypothesis HST : em_stk rsegs m LO SP0.
  Hypothesis HT : em_at rsegs m (BA_FR + 72) ba_tbl.
  Hypothesis DsT : ly_dj LO SP0 (BA_FR + 72) (BA_FR + 240).
  Hypothesis Hdb : length db = 6%nat.
  Hypothesis HD : em_at rsegs m d db.
  Hypothesis Dsd : ly_dj LO SP0 d (d + 6).
  Hypothesis Hsb : length sb = 6%nat.
  Hypothesis HSb : em_at rsegs m s sb.
  Hypothesis Dss : ly_dj LO SP0 s (s + 6).
  Hypothesis HM : md <> 0 -> md mod 8 = 0 /\ md + 296 <= 2^64 /\ length mb = 296%nat /\ em_at rsegs m md mb /\
                             ly_dj LO SP0 md (md + 296).
  Hypothesis HN : md <> 0 -> NM -> name_ok nb /\ em_at rsegs m (rname mb) nb /\
                                   ly_dj LO SP0 (rname mb) (rname mb + Z.of_nat (length nb)).
  Hypothesis Ho1492 : o <> 0 -> o + 1492 <= 2^64.
  Hypothesis HEo : GO && EE = true ->
       rw_cells rsegs m o [CB (Z.to_nat LEN) junk] /\ ly_dj LO SP0 o (o + LEN) /\
       ly_dj o (o + LEN) (BA_FR + 72) (BA_FR + 240) /\ ly_dj o (o + LEN) md (md + 296) /\
       (NM -> ly_dj o (o + LEN) (rname mb) (rname mb + Z.of_nat (length nb))) /\
       ly_dj o (o + LEN) d (d + 6) /\ ly_dj o (o + LEN) s (s + 6).
  Hypothesis MI0 : em_mi rsegs m.

  Definition RESb (m' : word -> option byte) : Prop :=
    bytes_at rsegs m' o
      (em_fr db sb (bv_unsigned a5 mod 65536) (Z_to_bv 8 205) (Z_to_bv 8 234) (ba_X md mb nb b) LEN)
    /\ em_wok NN = true
    /\ (b <= 1 -> blocksum (ba_X md mb nb b) = 0)
    /\ (blocksum (ly_Z md mb nb b) = 0 -> ba_X md mb nb b = ly_Z md mb nb b).

  Definition Qb : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                      (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 RR)
                    a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch [(LO, SP0); (o, o + RR)] m m'
      /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' LO SP0
      /\ (GO = false -> munch [(SP0 - 80, SP0)] m m')
      /\ (GO && EE = true -> RESb m').

  Lemma rng_sp : 352 <= SP0 < 2^64.
  Proof. pose proof (zr_word sp) as R. unfold inr64 in R. destruct HST as (H1 & _). lia. Qed.

  Lemma frame_sub : forall r, sub_fp [(SP0 + -80, SP0)] [(LO, SP0); (o, o + r)].
  Proof. intros r x Hx. cbn [outside] in *. destruct Hx as [H1 _]. split; [lia | exact I]. Qed.

  (* 0x1476c: a refusal returns 0. *)
  Lemma fail : forall (x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                      u3 u4 u5 u6 : word) (mc : word -> option byte) (j : list byte),
    GO = false ->
    rw_cells rsegs mc (SP0 + -80) [CB 8 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -80) ->
    munch [(SP0 + -80, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evt rsegs Qb
      (MS (mkR x1 (Z_to_bv 64 (SP0 + -80)) gp tp u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
               x22 x23 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x1476c) fc None mc (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 u3 u4 u5 u6 mc j
      HG FR ST MU WM MI.
    pose proof rng_sp as Rsp. pose proof ST as (Rlo & _ & _).
    do 12 step.
    apply evt_done. unfold Qb.
    replace RR with 0 by (rewrite HG; reflexivity).
    do 14 eexists. exists mc.
    split; [reflexivity|].
    split; [exact (munch_weaken _ _ m mc (frame_sub 0) MU)|].
    split; [exact WM|]. split; [exact MI|].
    split; [release_frame FR ST (bv_unsigned sp); exact ST|].
    split.
    - intros _. apply (munch_weaken [(SP0 + -80, SP0)]); [|exact MU].
      intros x Hx. cbn [outside] in *. destruct Hx as [H1 _]. split; [lia | exact I].
    - rewrite HG. intros H. cbn [andb] in H. discriminate H.
  Qed.

  (* 0x14710: the width, the frame pops, and the tail jump to ctrl_emit_as. *)
  Lemma tail : forall (u0 u1 u2 x10 x11 x12 x13 x14 u3 u4 u5 u6 : word) (mc : word -> option byte)
                      (j : list byte) (f : Z),
    GO = true -> f = BA_FR + 24 * ba_row b ->
    rw_cells rsegs mc (SP0 + -80) [CB 8 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mc LO (SP0 + -80) ->
    munch [(SP0 + -80, SP0)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
    evt rsegs Qb
      (MS (mkR ra (Z_to_bv 64 (SP0 + -80)) gp tp u0 u1 u2 (Z_to_bv 64 ns) a6 x10 x11 x12 x13 x14 a5 a6
               (Z_to_bv 64 ns) a5 (Z_to_bv 64 s) (Z_to_bv 64 d) (Z_to_bv 64 md) (Z_to_bv 64 o) (Z_to_bv 64 f)
               s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x14710) fc None mc (seg_rom rsegs)).
  Proof.
    intros u0 u1 u2 x10 x11 x12 x13 x14 u3 u4 u5 u6 mc j f HG -> FR ST MU WM MI.
    pose proof rng_sp as Rsp. pose proof ST as (Rlo & _ & _).
    pose proof HG as HG'. apply andb_true_iff in HG' as [HG1 Hb6]. apply andb_true_iff in HG1 as [Ho0 Hm0].
    apply negb_true_iff, Z.eqb_neq in Ho0. apply negb_true_iff, Z.eqb_neq in Hm0. apply Z.leb_le in Hb6.
    assert (Hb6' : 0 <= b <= 6) by lia.
    destruct (ba_facts b Hb6') as (FK & KR & FBB & FC & FL & FG & FA & F18 & F19 & FAO & FAL).
    destruct (HM Hm0) as (M8 & M296 & ML & HMm & DM).
    pose proof DM as DMu. unfold ly_dj in DMu.
    pose proof (em_obj0 rsegs m mc (SP0 + -80) SP0 md mb 296 MU HMm ltac:(rewrite ML; reflexivity)
                  ltac:(lia)) as HMc.
    pose proof (bm_uw_range md (firstn 8 (skipn 16 mb))) as RN.
    (* reac_box_model_upstream_width(m) *)
    step. step.
    eapply evt_cut.
    { eapply HUW with (mp := md) (bs := firstn 8 (skipn 16 mb)).
      - rewrite unsigned_lit by lia. reflexivity.
      - intros _. split; [lia|]. split.
        + rewrite length_firstn, length_skipn, ML. reflexivity.
        + pose proof (ly_bytes_sub rsegs mc md mb 16 8 HMc ltac:(rewrite ML; lia)) as H16.
          change (Z.of_nat 16) with 16 in H16. exact H16. }
    intros ms' (y1 & y2 & y3 & y4 & ->). fixret.
    (* the arguments, the restores and the jump *)
    do 21 step.
    release_frame FR ST (bv_unsigned sp).
    (* the facts ctrl_emit_as needs, in the memory at the jump *)
    pose proof DsT as DsTu. unfold ly_dj in DsTu.
    pose proof (ba_row_at rsegs mc b
                  (em_obj0 rsegs m mc (SP0 + -80) SP0 (BA_FR + 72) ba_tbl 168 MU HT ltac:(vm_compute; reflexivity)
                     ltac:(lia)) Hb6')
      as HRc.
    pose proof Dsd as Dsdu. unfold ly_dj in Dsdu. pose proof Dss as Dssu. unfold ly_dj in Dssu.
    pose proof (em_obj0 rsegs m mc (SP0 + -80) SP0 d db 6 MU HD ltac:(rewrite Hdb; reflexivity) ltac:(lia)) as HDc.
    pose proof (em_obj0 rsegs m mc (SP0 + -80) SP0 s sb 6 MU HSb ltac:(rewrite Hsb; reflexivity) ltac:(lia)) as HSc.
    assert (NMc : forall X : Prop, (NM -> X) ->
              (3 <= ly_k (ba_fr (ba_row b)) <= 9 /\
               (ly_bb (ly_k (ba_fr (ba_row b))) = 5 \/ ly_bb (ly_k (ba_fr (ba_row b))) = 6)) /\
              has mb <> 0 /\ rname mb <> 0 -> X).
    { intros X HX ((_ & B56) & H1 & H2). apply HX. rewrite FK, FBB in B56. split; [exact B56 | split; assumption]. }
    pose proof HEA as HE. unfold ctrl_emit_as_contract, CTRL_EMIT_AS_K in HE. cbv zeta in HE.
    eapply evt_cut.
    { eapply HE with (o := o) (f := BA_FR + 24 * ba_row b) (md := md) (d := d) (s := s) (g := 0) (n := NN)
        (ns := ns) (row := ba_fr (ba_row b)) (tb := []) (mb := mb) (nb := nb) (gb := []) (db := db) (sb := sb)
        (junk := junk).
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - lia.
      - lia.
      - lia.
      - exact HS16.
      - exact ST.
      - apply (em_dj_sub _ _ _ _ _ _ _ _ DsT); lia.
      - intros K2. exfalso. rewrite FK in K2. lia.
      - exact DM.
      - apply NMc. intros NMx. destruct (HN Hm0 NMx) as (_ & _ & DN). exact DN.
      - exact Dsd.
      - exact Dss.
      - intros G0. exfalso. exact (G0 eq_refl).
      - unfold BA_FR. lia.
      - unfold BA_FR. lia.
      - unfold BA_FR. lia.
      - apply ba_fr_len.
      - exact HRc.
      - rewrite FK. lia.
      - rewrite FC. destruct (b <=? 1); lia.
      - lia.
      - lia.
      - lia.
      - rewrite FAO, FAL. lia.
      - intros K2. exfalso. rewrite FK in K2. lia.
      - rewrite FC. destruct (b <=? 1); intros C2; exfalso; lia.
      - intros L2. lia.
      - exact Hm0.
      - exact M8.
      - exact M296.
      - exact ML.
      - exact HMc.
      - apply NMc. intros NMx. destruct (HN Hm0 NMx) as (NO & NB & DN). split; [exact NO|].
        pose proof DN as DNu. unfold ly_dj in DNu.
        exact (em_obj0 rsegs m mc (SP0 + -80) SP0 _ nb _ MU NB eq_refl ltac:(lia)).
      - lia.
      - exact (Ho1492 Ho0).
      - rewrite (ba_E_eq b NN mb Hb6'), (ba_len_eq b NN Hb6'). intros E1.
        assert (GE : GO && EE = true) by (rewrite HG; exact E1).
        destruct (HEo GE) as (HO & Dso & DoT & Dom & Don & Dod & Dos).
        pose proof Dso as Dsou. unfold ly_dj in Dsou.
        split.
        { apply (rw_cells_transport rsegs [(SP0 + -80, SP0)] m mc o _ HO MU WM).
          cbn [disjoint_from cells_size csize]. lia. }
        split; [exact Dso|]. split; [apply (em_dj_sub _ _ _ _ _ _ _ _ DoT); lia|].
        split; [intros K2; exfalso; rewrite FK in K2; lia|].
        split; [exact Dom|]. split; [apply NMc; exact Don|].
        split; [exact Dod|]. split; [exact Dos|].
        intros G0. exfalso. exact (G0 eq_refl).
      - exact Hdb.
      - exact HDc.
      - exact Hsb.
      - exact HSc.
      - intros G0. exfalso. exact (G0 eq_refl).
      - intros _. lia.
      - exact MI. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> &
                MU' & WM' & MI' & ST' & RES').
    apply evt_done. unfold Qb.
    rewrite (ba_E_eq b NN mb Hb6'), (ba_len_eq b NN Hb6') in MU'. rewrite (ba_E_eq b NN mb Hb6') in RES'.
    rewrite (ba_E_eq b NN mb Hb6'), (ba_len_eq b NN Hb6').
    rewrite HG. cbn [andb].
    do 14 eexists. exists m'.
    split; [reflexivity|].
    split; [exact (munch_trans _ m mc m' (munch_weaken _ _ m mc (frame_sub _) MU) MU')|].
    split; [exact (wmono_trans rsegs m mc m' WM WM')|]. split; [exact MI'|]. split; [exact ST'|].
    split; [intros H; discriminate H|].
    intros E1. destruct (RES' E1) as (B & W & CL).
    exact (ba_res rsegs m' o b md NN (bv_unsigned a5 mod 65536) mb nb [] [] db sb Hb6' B W CL).
  Qed.

  Lemma main : forall (t0 t1 t2 t3 t4 t5 t6 : word),
    evt rsegs Qb
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 md) (Z_to_bv 64 b) (Z_to_bv 64 d)
               (Z_to_bv 64 s) a5 a6 (Z_to_bv 64 ns) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14690) fc None m (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 t3 t4 t5 t6.
    pose proof rng_sp as Rsp.
    pose proof (HST : stk rsegs m (bv_unsigned sp - 352) (bv_unsigned sp)) as ST. pose proof ST as (Rlo & _ & _).
    pose proof (MI0 : mem_inv rsegs m) as MI.
    pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    step. carve_frame 80%nat ST. do 9 step.
    (* o = 0 *)
    step. rewrite rc_eqb by lia. destruct (Z.eqb_spec o 0) as [O0|O0]; cbv iota.
    { eapply fail; [apply ba_go_false; left; exact O0 | eassumption ..]. }
    (* m = 0 *)
    step. step. rewrite rc_eqb by lia. destruct (Z.eqb_spec md 0) as [M0|M0]; cbv iota.
    { eapply fail; [apply ba_go_false; right; left; exact M0 | eassumption ..]. }
    (* b > 6 *)
    step. step. step. rewrite rc_ltu by lia. destruct (Z.ltb_spec 6 b) as [B6|B6]; cbv iota.
    { eapply fail; [apply ba_go_false; right; right; exact B6 | eassumption ..]. }
    assert (HG : GO = true) by (apply ba_go_true; assumption).
    (* row(b) from RT and f = CTRL_FRAMES + 24 row(b) *)
    destruct (ba_cases b ltac:(lia)) as [Eb|[Eb|[Eb|[Eb|[Eb|[Eb|Eb]]]]]]; rewrite Eb; do 16 step;
      (eapply tail; [exact HG | rewrite Eb; reflexivity | eassumption ..]).
  Qed.
End Build.

Theorem reac_ctrl_build_as_holds :
  ctrl_emit_as_contract -> reac_box_model_upstream_width_contract -> reac_ctrl_build_as_contract.
Proof.
  intros HEA HUW. unfold reac_ctrl_build_as_contract, REAC_CTRL_BUILD_AS, REAC_CTRL_BUILD_AS_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m o md b d s ns mb nb db sb junk.
  cbv zeta.
  intros Ha0 Ha1 Ha2 Ha3 Ha4 -> Hns HS16 HST HT DsT Hdb HD Dsd Hsb HSb Dss HM HN Ho1492 HEo MI0.
  pose proof (rc_word_range a0 o Ha0) as Ro. apply rc_word in Ha0. subst a0.
  pose proof (rc_word_range a1 md Ha1) as Rmd. apply rc_word in Ha1. subst a1.
  pose proof (rc_word_range a2 b Ha2) as Rb. apply rc_word in Ha2. subst a2.
  apply rc_word in Ha3. subst a3.
  apply rc_word in Ha4. subst a4.
  eapply main; eassumption.
Qed.
