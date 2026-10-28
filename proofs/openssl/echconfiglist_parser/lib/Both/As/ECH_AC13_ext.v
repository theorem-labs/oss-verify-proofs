(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C5 ECH_AStmt_C13 ECH_AKit ECH_AsKit ECH_AC1_malloc ECH_AC1_free ECH_AC5_popfree.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.

  Definition AXF_RA : Z := R_ossl_echext_free_CRYPTO_free.   (* [comment removed for export] *)
  Definition AECHS_FILE : Z := 0x11238e.                      (* [comment removed for export] *)
  Definition SHB : Z := 0x7fff8000.
  Definition axf_frame (s2 s1 s0 ra : word) : list cell := [C8 s2; C8 s1; C8 s0; C8 ra].

  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  (* [comment removed for export] *)
  Lemma axf_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a lo : Z) (X : extrep) (pad : list byte),
      rw_cells asegs m a (ext_cells X pad) -> 0 < a -> a mod 16 = 0 -> a + EXT_SIZE <= lo -> 0 <= ex_val X < 2^64 ->
      accessible m a EXT_SIZE ->
      rw_cells asegs m AGOT_SHBASE [C8 (wz ASHBASE_CELL)] -> rw_cells asegs m ASHBASE_CELL [C8 (wz ASHADOW_BASE)] ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 AXF_RA) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 a)
                       (Z_to_bv 64 (ex_val X)) (Z_to_bv 64 AECHS_FILE) (Z_to_bv 64 60) a3 a4 a5 a6 a7
                       (Z_to_bv 64 AECHS_FILE) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp + -32)
          /\ rw_cells asegs m1 (bv_unsigned sp + -32) (axf_frame s2 s1 s0 ra)
          /\ rw_cells asegs m1 a (ext_cells X pad))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_ossl_echext_free) fc None m (seg_rom asegs)).
  Proof.
    intros until pad. intros XC POS AL16 BL VR ACC0 GSB SHB0 ST CEIL LO MI. unfold P_ossl_echext_free, P_CRYPTO_free, AXF_RA, R_ossl_echext_free_CRYPTO_free, AECHS_FILE.
    unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    unfold ext_cells, wz in XC. pose proof (rw_cells_bound _ _ _ _ XC) as XB. cbn [cells_size csize Nat.add] in XB. unfold EXT_SIZE in *.
    acb. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof ACC0 as (_ & AHI & _). unfold AAPP_HI in AHI.
    pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof ACC0 as ACC'. clear ACC0. change (id (accessible m a 16)) in ACC'.
    carve_frame 32%nat ST.
    do 6 step. step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACC : accessible mx a 16) by (unfold id in ACC'; eapply accessible_across; [exact ACC'| exact MU|]; constructor; [cbn; unfold AHI_LO in *; lia| constructor]) end.
    clear ACC'.
    (* [comment removed for export] *)
    step. step. ubal_by AL16. step. if_lit. step. step. step. zstep. zstep. zstep. ck8_check ACC (a + 8).
    (* [comment removed for export] *)
    step. step. step. step. step. step. step.
    finish.
  Qed.

  (* [comment removed for export] *)
  Lemma axf_seg2 :
    forall (sp gp tp t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a : Z),
      rw_cells asegs m (bv_unsigned sp + -32) (axf_frame s2 s1 s0 ra) -> mem_inv asegs m ->
      evt asegs (fun ms' => exists t1' : word, ms' = MS (mkR ra sp gp tp t0 t1' t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 AECHS_FILE) (Z_to_bv 64 61) a3 a4 a5 a6 a7
                                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AXF_RA) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0x (Z_to_bv 64 a) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 AECHS_FILE) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AXF_RA)) fc None m (seg_rom asegs)).
  Proof.
    intros until a. intros FR MI. unfold AXF_RA, R_ossl_echext_free_CRYPTO_free, AECHS_FILE, P_CRYPTO_free.
    replace (ret_pc (Z_to_bv 64 0x552658)) with (Z_to_bv 64 0x552658) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (aword_range sp) as SPR. unfold axf_frame in FR.
    do 10 step. finish.
  Qed.
End S.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  (* [comment removed for export] *)
  Definition acfree_opt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (P : Z) (o : oblk) (lo B : Z) (errv : word) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : as_St H) (LB' : list block),
      as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
      /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv] /\ as_rauxv_ok H m' B
      /\ Permutation (blocks_of P o ++ LB') LB /\ (forall b, In b LB' -> In b LB)
      /\ xpres H LB' (bv_unsigned sp) [] m m'
      /\ as_RHEAP H s' LB' m'
      /\ IMPL_mem m' /\ GOT_mem m'
      /\ as_AL H s' >= as_AL H s - ocost H o.
  Lemma acfree_opt_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (P : Z) (o : oblk) (lo B : Z) (errv : word)
           (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 P -> (match o with None => P = 0 | Some (id, n) => In (id, P, n) LB end) -> oshad m P o ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - CFREE_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 -> ACONST m ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') -> pf_ok (as_TR H) PF_cfree (bv_unsigned ra) CH ->
      ocost H o <= as_AL H s ->
      IMPL_mem m -> GOT_mem m ->
      as_SR H (acfree_opt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB P o lo B errv m mo) (mkCfg msF mo).
  Proof.
    intros until CH. intros VIS A0 HO OSH HP KREL AUX SPB ST CEIL LO ERR MI TP SP16 AC CHN CHS PF HAL IM GM. subst a0.
    acb. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (SUBL : forall p L b, In b (as_lb_remove H p L) -> In b L) by (intros p L b Hb; eapply (proj2 (proj2 (ah_lb_remove H HH))); exact Hb).
    destruct o as [[id n]|].
    - (* [comment removed for export] *)
      cbn [oshad] in OSH. destruct OSH as (TOP & SH & bs & CB). pose proof SH as [N0 _].
      cbn [ocost] in HAL. rewrite (Z.max_l n 0) in HAL by exact N0.
      pose proof (acfree_spec H HH) as CF. unfold cfree_stmt in CF.
      eapply (ah_mono H HH).
      { eapply CF with (lo := lo) (B := B) (LB := LB) (s := s) (p := id) (n := n) (errv := errv) (CH := CH);
          [exact VIS| reflexivity| ..].
        all: first [exact HP| exact KREL| exact HO| exact AUX| exact SPB| exact ST| exact CEIL| exact LO| exact ERR| exact MI| exact TP| exact SP16| exact AC
                   | exact CHN| exact CHS| exact PF| exact HAL| exact CB| exact SH| exact IM| exact GM| match goal with |- ?G => idtac "LEFT:" G end]. }
      intros [ms2 mo2] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
      destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & s' &
                      E & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & XP2 & HEAP2 & IM2 & GM2 & AL2).
      unfold acfree_opt_post. cbn [cfg_ms cfg_model].
      exists u0, u1, u2, b0, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, s', (as_lb_remove H id LB).
      split; [exact E|]. split; [exact KREL2|]. split; [exact MP2|]. split; [exact MI2|]. split; [exact AC2|]. split; [exact ST2|].
      split; [exact ERR2|]. split; [exact AUX2|].
      split; [cbn [blocks_of app]; eapply (alb_remove_perm H HH); [exact HP| exact HO]|].
      split; [intros b Hb; eapply SUBL; exact Hb|].
      split; [exact XP2|]. split; [exact HEAP2|]. split; [exact IM2|]. split; [exact GM2|]. cbn [ocost]. rewrite (Z.max_l n 0) by exact N0. exact AL2.
    - (* [comment removed for export] *)
      subst P. pose proof (acfree_null_spec H HH) as CF. unfold cfree_null_stmt in CF.
      eapply (ah_mono H HH).
      { eapply CF with (lo := lo) (B := B) (LB := LB) (s := s) (errv := errv) (CH := CH); [exact VIS| ..].
        all: first [exact HP| exact KREL| exact AUX| exact SPB| exact ST| exact CEIL| exact LO| exact ERR| exact MI| exact TP| exact SP16| exact AC
                   | exact CHN| exact CHS| exact HAL| exact IM| exact GM| match goal with |- ?G => idtac "LEFT0:" G end]. }
      intros [ms2 mo2] PO. unfold cfree_null_post in PO. cbn [cfg_ms cfg_model] in PO.
      destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & s' &
                      E & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & XP2 & HEAP2 & IM2 & GM2 & AL2).
      unfold acfree_opt_post. cbn [cfg_ms cfg_model].
      exists u0, u1, u2, b0, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, s', LB.
      split; [exact E|]. split; [exact KREL2|]. split; [exact MP2|]. split; [exact MI2|]. split; [exact AC2|]. split; [exact ST2|].
      split; [exact ERR2|]. split; [exact AUX2|].
      split; [cbn [blocks_of app]; apply Permutation_refl|]. split; [intros b Hb; exact Hb|].
      split; [exact XP2|]. split; [exact HEAP2|]. split; [exact IM2|]. split; [exact GM2|]. cbn [ocost]. exact AL2.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma EXTobj_frame_law : EXTobj_frame H.
  Proof.
    unfold EXTobj_frame, EP_frame. intros LB LB' m m' p x SP ((pad & PL & HC) & HIN & OF) KEEP XP BEL.
    unfold EXTobj. split; [| split; [apply KEEP; left; reflexivity|]].
    - exists pad. split; [exact PL|]. eapply (xpres_rw_cells' H); [exact XP| exact HC| | constructor].
      right; right; left. exists (ex_id x, p, EXT_SIZE). split; [apply KEEP; left; reflexivity|]. unfold ext_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold EXT_SIZE. lia.
    - revert OF KEEP. unfold blocks_EXT. destruct (ex_val_o x) as [[vid vn]|]; cbn [ofield blocks_of]; intros OF KEEP; [| exact OF].
      destruct OF as (O1 & O2 & O3). split; [exact O1|]. split; [exact O2|]. apply KEEP. right. left. reflexivity.
  Qed.

  Lemma EXTobj_owned_law : EP_owned extrep EXTobj blocks_EXT.
  Proof.
    unfold EP_owned. intros LB m p x (HC & HIN & OF) b Hb.
    unfold blocks_EXT in Hb. destruct Hb as [<-|Hb]; [exact HIN|].
    revert OF Hb. destruct (ex_val_o x) as [[vid vn]|]; cbn [blocks_of ofield]; intros OF Hb; [| destruct Hb].
    destruct Hb as [<-|[]]. destruct OF as (_ & _ & O3). exact O3.
  Qed.

  Lemma GOT_echfree_frame : G_frame H GOT_echfree.
  Proof.
    unfold G_frame, GOT_echfree. intros LB SP m m' GM XP CE. acb.
    eapply (xpres_rw_cells' H); [exact XP| exact GM| | constructor].
    right; left. intros a Ha. cbn [cells_size csize Nat.add] in Ha. unfold A_got_ossl_echext_free in Ha. unfold aimg_client. lia.
  Qed.
  Lemma GOT_echfree_across : forall W m m1,
    munch W m m1 -> wmono asegs m m1 -> disjoint_from W A_got_ossl_echext_free 16 -> GOT_echfree m -> GOT_echfree m1.
  Proof. intros W m m1 MU WM DJ GM. eapply rw_cells_transport; [exact GM| exact MU| exact WM| exact DJ]. Qed.
  Lemma GOT_echfree_xpres : forall LB SP X m m1,
    xpres H LB SP X m m1 -> aceil <= SP -> Forall (fun iv : Z * Z => A_got_ossl_echext_free + 16 <= fst iv \/ snd iv <= A_got_ossl_echext_free) X ->
    GOT_echfree m -> GOT_echfree m1.
  Proof.
    intros LB SP X m m1 XP CE FX GM. acb. eapply (xpres_rw_cells' H); [exact XP| exact GM| | exact FX].
    right; left. intros a Ha. cbn [cells_size csize Nat.add] in Ha. unfold A_got_ossl_echext_free in Ha. unfold aimg_client. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma addressable_xpres_blk : forall LB2 m m' SP p A n,
    In (p, A, n) LB2 -> A + n <= AAPP_HI -> addressable m A n -> xpres H LB2 SP [] m m' -> addressable m' A n.
  Proof.
    intros LB2 m m' SP p A n IN Htop (Hn & A0 & A8 & (B0 & B1 & BA) & (W0 & W1 & WA)) XP. acb.
    assert (CL : forall i, 0 <= i < nsh n -> m' (wa (sh A + i)) = m (wa (sh A + i)) /\ (wview asegs m (wa (sh A + i)) <> None -> wview asegs m' (wa (sh A + i)) <> None)).
    { intros i Hi. apply XP.
      - unfold nsh in Hi. unfold sh, AAPP_HI in *. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia.
      - split; [| intros []]. right; right; right; left. exists (p, A, n). split; [exact IN|]. cbn [blk_addr blk_size fst snd]. lia. }
    split; [exact Hn|]. split; [exact A0|]. split; [exact A8|]. split.
    - split; [exact B0|]. split; [exact B1|].
      intros i Hi. rewrite <- (BA i Hi). unfold mrd. destruct (CL (Z.of_nat i) ltac:(pose proof (shadow_of_length n Hn); lia)) as [E _]. rewrite E. reflexivity.
    - split; [exact W0|]. split; [exact W1|].
      intros i Hi. destruct (CL i ltac:(pose proof (shadow_of_length n Hn); lia)) as [_ Wp]. apply Wp. apply WA. exact Hi.
  Qed.
  Lemma oshad_xpres : forall LB2 m m' SP P o,
    (match o with None => True | Some (id, n) => In (id, P, n) LB2 end) -> oshad m P o -> xpres H LB2 SP [] m m' -> oshad m' P o.
  Proof.
    intros LB2 m m' SP P [[id n]|] IN OSH XP; [| exact I]. cbn [oshad] in *. destruct OSH as (TOP & SH & bs & CB).
    split; [exact TOP|]. split; [eapply addressable_xpres_blk; [exact IN| exact TOP| exact SH| exact XP]|].
    exists bs. eapply (xpres_rw_cells' H); [exact XP| exact CB| | constructor].
    right; right; left. exists (id, P, n). split; [exact IN|]. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. pose proof SH as [Hn _]. lia.
  Qed.

  Lemma EXT_shad_frame_law : EXT_shad_frame H.
  Proof.
    unfold EXT_shad_frame, eshad_frame. intros LB' m m' p x SP (TOP & SH & OSH) KEEP XP BEL.
    split; [exact TOP|]. split.
    - eapply addressable_xpres_blk; [apply KEEP; left; reflexivity| exact TOP| exact SH| exact XP].
    - eapply oshad_xpres; [| exact OSH| exact XP]. unfold blocks_EXT in KEEP. destruct (ex_val_o x) as [[vid vn]|]; [| exact I].
      apply KEEP. right. left. reflexivity.
  Qed.

  Lemma ocost_pos : forall o, 0 <= ocost H o.
  Proof.
    intros [[? n]|]; cbn [ocost]; apply (proj1 (proj2 (proj2 (ah_costs H HH)))); lia.
  Qed.
  Lemma ext_cost_pos : ecost_pos extrep (ext_cost H).
  Proof.
    unfold ecost_pos, ext_cost. intros x. pose proof (ocost_pos (ex_val_o x)).
    pose proof (proj1 (proj2 (proj2 (ah_costs H HH))) EXT_SIZE ltac:(unfold EXT_SIZE; lia)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma oshad_across : forall W m m1 P o,
    oshad m P o -> munch W m m1 -> wmono asegs m m1 ->
    (match o with None => True | Some (id, n) => disjoint_from W P n /\ disjoint_from W (sh P) (nsh n) end) -> oshad m1 P o.
  Proof.
    intros W m m1 P [[id n]|] OSH MU WM DJ; [| exact I]. cbn [oshad] in *. destruct OSH as (TOP & SH & bs & CB). destruct DJ as [DJ1 DJ2].
    split; [exact TOP|]. split; [eapply addressable_transport; [exact SH| exact MU| exact WM| exact DJ2]|].
    exists bs. eapply rw_cells_transport; [exact CB| exact MU| exact WM|]. cbn [cells_size csize Nat.add]. pose proof SH as [Hn _]. replace (Z.of_nat (Z.to_nat n + 0)) with n by lia. exact DJ1.
  Qed.

  (* [comment removed for export] *)
  Lemma aextfree_spec : extfree_stmt H.
  Proof.
    unfold extfree_stmt, efree_stmt_at. intros until CH.
    intros VIS A0 XO XSH ND HP KREL AUX SPB ST CEIL LO ERR MI TP SP16 AC CHN CHS PF HAL IM GM GG RAE. subst a0.
    unfold EXTFREE_STACK, FR_ossl_echext_free, CFREE_STACK, AFREE_STACK in LO.
    acb. subst tp. rewrite unsigned_lit in ERR by (unfold ATP; lia).
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (CSP0 : aceil <= bv_unsigned sp) by lia. assert (CSP : aceil <= bv_unsigned sp + -32) by lia.
    pose proof (ACONST_shbase m AC) as [GSB SHB0].
    pose proof XO as XO'. destruct XO' as ((pad & PL & XC) & HIN & OF). pose proof XSH as (TOP & SH & OSH).
    pose proof (ah_blocks H HH _ _ _ _ HP HIN) as (K1 & K2 & K3 & K4 & K5 & K6 & K7). cbn [blk_addr blk_size fst snd] in K1, K2, K3, K4, K5, K6, K7.
    unfold AIMG_TOP in K4. unfold EXT_SIZE in K3, K5, K7, TOP. unfold AAPP_HI in TOP.
    pose proof (aapp_bounds p 16 K7 ltac:(lia)) as (AB1 & AB2 & AB3 & AB4 & AB5). unfold AAPP_HI in AB3. clear K6.
    assert (SUBL : forall q L b, In b (as_lb_remove H q L) -> In b L) by (intros q L b Hb; eapply (proj2 (proj2 (ah_lb_remove H HH))); exact Hb).
    assert (VR : 0 <= ex_val x < 2^64).
    { clear - OF HP HH ACEILB. revert OF. destruct (ex_val_o x) as [[vid vn]|]; cbn [ofield]; intros OF; [| lia]. destruct OF as (O1 & O2 & O3).
      pose proof (ah_blocks H HH _ _ _ _ HP O3) as (E1 & _ & _ & _ & E5 & _). cbn [blk_addr blk_size fst snd] in E1, E5. lia. }
    assert (ACC0 : accessible m p EXT_SIZE) by (unfold EXT_SIZE in *; eapply addressable_accessible; [exact SH| lia| lia| unfold AAPP_HI; lia]).
    pose proof (proj1 (proj2 (proj2 (ah_costs H HH))) 16 ltac:(lia)) as CF16. pose proof (ocost_pos (ex_val_o x)) as CFO.
    unfold ext_cost in HAL. unfold EXT_SIZE in HAL.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply axf_seg1 with (lo := lo);
      [exact XC| exact K1| exact K2| unfold EXT_SIZE; lia| exact VR| exact ACC0| exact GSB| exact SHB0| exact ST| exact CEIL| lia| exact MI]|].
    intros msF1 mo1 KREL1 MP1 (m1 & VIS1 & MU1 & WM1 & MI1 & ST1 & FR1 & XC1).
    assert (CW : Forall (aclient_write_ok H LB) [(bv_unsigned sp + -32, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (AW : Forall aconst_ok [(bv_unsigned sp + -32, bv_unsigned sp)])
      by (constructor; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| constructor]).
    assert (HP1 : as_RHEAP H s LB m1) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW]).
    assert (AUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW]).
    assert (AC1 : ACONST m1) by (eapply ACONST_frame; [exact AC| exact MU1| exact WM1| exact AW]).
    assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]) by (eapply errno_across; [exact ERR| exact MU1| exact WM1| unfold ATP; cbn; lia]).
    assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]).
    assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]).
    assert (GG1 : GOT_echfree m1) by (eapply GOT_echfree_across; [exact MU1| exact WM1| unfold A_got_ossl_echext_free; cbn; lia| exact GG]).
    assert (XP1 : xpres H LB (bv_unsigned sp) [] m m1)
      by (eapply (xpres_of_munch H s LB _ [] _ m m m1); [exact HH| exact HP| exact MU1| exact WM1|]; constructor; [left; cbn; lia| constructor]).
    assert (SHH1 : addressable m1 p 16).
    { unfold EXT_SIZE in SH. eapply addressable_transport; [exact SH| exact MU1| exact WM1|].
      pose proof (sh_aapp_range p 16 K7 ltac:(lia)) as (S1 & S2 & S3). unfold AHI_LO in S3. pose proof aceil_range. cbn. lia. }
    assert (OSH1 : oshad m1 (ex_val x) (ex_val_o x)).
    { eapply oshad_across; [exact OSH| exact MU1| exact WM1|]. clear - OF HP HH ACEILB CSP CSP0 SPR. revert OF. destruct (ex_val_o x) as [[vid vn]|]; cbn [ofield]; intros OF; [| exact I].
      destruct OF as (O1 & O2 & O3). pose proof (ah_blocks H HH _ _ _ _ HP O3) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). cbn [blk_addr blk_size fst snd] in E1, E2, E3, E4, E5, E6, E7.
      pose proof (sh_aapp_range (ex_val x) vn E7 ltac:(lia)) as (S1 & S2 & S3). unfold AHI_LO in S3. pose proof aceil_range. cbn. lia. }
    assert (CH0 : as_chain H m1 (bv_unsigned s0) CH)
      by (eapply (achain_below H HH m m1); [exact CHN| exact CHS| exact MU1|]; constructor; [left; cbn; lia| constructor]).
    assert (CH1 : as_chain H m1 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (ah_chain_cons H HH); [exact CH0| lia| lia| exact SP16| lia| lia|].
      pose proof FR1 as FR2. unfold axf_frame in FR2.
      change ([C8 s2; C8 s1; C8 s0; C8 ra]) with ([C8 s2; C8 s1] ++ [C8 s0; C8 ra]) in FR2.
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR2. destruct FR2 as [_ FR2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul] in FR2.
      replace (bv_unsigned sp - 16) with (bv_unsigned sp + -32 + 16) by lia.
      first [exact FR2 | revert FR2; rewrite !Z_to_bv_bv_unsigned; intros FR2; exact FR2]. }
    assert (CHS1 : forall fp' ra', In (fp', ra') ((bv_unsigned sp, bv_unsigned ra) :: CH) -> bv_unsigned sp + -32 + 16 <= fp')
      by (intros fp' ra' [E|Hin]; [injection E as <- <-; lia| specialize (CHS _ _ Hin); lia]).
    assert (SP16' : (bv_unsigned sp + -32) mod 16 = 0) by (replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) by lia; rewrite Zminus_mod, SP16; reflexivity).
    clear CW AW.
    (* [comment removed for export] *)
    eapply (ah_seq H HH).
    { eapply acfree_opt_spec with (lo := lo) (B := B) (LB := LB) (s := s) (P := ex_val x) (o := ex_val_o x) (errv := errv) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
        [exact VIS1| reflexivity| ..]; rewrite ?unsigned_lit by (unfold AXF_RA, R_ossl_echext_free_CRYPTO_free; lia).
      all: first [exact HP1| exact KREL1| exact OSH1| exact AUX1| exact ST1| exact CEIL| exact ERR1| exact MI1| reflexivity| exact SP16'| exact AC1| exact CH1| exact CHS1
                 | exact IM1| exact GM1| unfold CFREE_STACK, AFREE_STACK; lia
                 | unfold AXF_RA; eapply pf_ok_call; [exact PF|]; unfold PF_extfree; intros y Hy; apply in_app_iff; left; exact Hy
                 | clear - OF; revert OF; destruct (ex_val_o x) as [[vid vn]|]; cbn [ofield]; intros OF; [destruct OF as (_ & _ & O3); exact O3| exact OF]
                 | lia | match goal with |- ?G => idtac "LEFT:" G end]. }
    intros [msF2 mo2] PO. unfold acfree_opt_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & s2' & LB2 &
                    VIS2 & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & PERM2 & SUB2 & XP2 & HEAP2 & IM2 & GM2 & AL2).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST2, XP2 by lia.
    assert (HIN2 : In (ex_id x, p, EXT_SIZE) LB2).
    { eapply perm_in_rest; [exact PERM2| exact HIN|]. clear - ND. unfold blocks_EXT in ND. intros Kb.
      revert ND Kb. destruct (ex_val_o x) as [[vid vn]|]; cbn [blocks_of map app]; intros ND Kb; [| destruct Kb]. destruct Kb as [Kb|[]].
      inversion ND as [|i l NI ND']; subst. apply NI. left. rewrite <- Kb. reflexivity. }
    assert (GG2 : GOT_echfree m2) by (eapply GOT_echfree_xpres; [exact XP2| exact CSP| constructor| exact GG1]).
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -32) (axf_frame s2 s1 s0 ra)) by (eapply (xpres_rw_cells' H); [exact XP2| exact FR1| left; cbn; lia| constructor]).
    assert (XC2 : rw_cells asegs m2 p (ext_cells x pad)).
    { eapply (xpres_rw_cells' H); [exact XP2| exact XC1| | constructor]. right; right; left. exists (ex_id x, p, EXT_SIZE).
      split; [exact HIN2|]. unfold ext_cells. cbn [cells_size csize Nat.add blk_addr blk_size fst snd]. unfold EXT_SIZE. lia. }
    assert (SHH2 : addressable m2 p 16) by (eapply addressable_xpres_blk; [exact HIN2| unfold AAPP_HI; lia| exact SHH1| exact XP2]).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply axf_seg2; [exact FR2| exact MI2]|].
    intros msF3 mo3 KREL3 MP3 (t1x & VIS3).
    (* [comment removed for export] *)
    unfold axf_frame in FR2. release_frame FR2 ST2 (bv_unsigned sp). rename ST2 into ST3.
    pose proof (rw_cells_flatten _ _ _ _ XC2) as XCB. unfold ext_cells in XCB. cbn [cells_size csize Nat.add] in XCB.
    assert (CH2 : as_chain H m2 (bv_unsigned s0) CH).
    { eapply (chain_via_apres H HH); [exact CH0| apply (xpres_nil_apres H); exact XP2| intros fp' ra' Hin; specialize (CHS _ _ Hin); lia]. }
    pose proof (acfree_spec H HH) as CF. unfold cfree_stmt in CF.
    eapply (ah_mono H HH).
    { eapply CF with (lo := lo) (B := B) (LB := LB2) (s := s2') (p := ex_id x) (n := EXT_SIZE) (errv := errv) (CH := CH);
        [exact VIS3| reflexivity| ..]; rewrite ?unsigned_lit by (unfold ATP; lia).
      all: first [exact HEAP2| exact KREL3| exact HIN2| exact AUX2| exact SPB| exact ST3| exact CEIL| exact ERR2| exact MI2| reflexivity| exact SP16| exact AC2| exact CH2| exact CHS
                 | exact XCB| unfold EXT_SIZE; exact SHH2| exact IM2| exact GM2| unfold CFREE_STACK, AFREE_STACK; lia
                 | eapply pf_ok_incl; [exact PF|]; unfold PF_extfree; intros y Hy; apply in_app_iff; right; exact Hy
                 | unfold EXT_SIZE; lia | match goal with |- ?G => idtac "LEFT2:" G end]. }
    intros [msF4 mo4] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m4 & s4' &
                    VIS4 & KREL4 & MP4 & MI4 & AC4 & ST4 & ERR4 & AUX4 & XP4 & HEAP4 & IM4 & GM4 & AL4).
    unfold efree_post. cbn [cfg_ms cfg_model].
    exists v0, v1, v2, c0, c1, c2, c3, c4, c5, c6, c7, v3, v4, v5, v6, m4, s4', (as_lb_remove H (ex_id x) LB2).
    split; [exact VIS4|]. split; [exact KREL4|]. split; [eapply (ah_mpres_trans H HH); [| exact MP4]; eapply (ah_mpres_trans H HH); [| exact MP3]; eapply (ah_mpres_trans H HH); [exact MP1| exact MP2]|].
    split; [exact MI4|]. split; [exact AC4|]. split; [exact ST4|].
    split; [rewrite unsigned_lit by (unfold ATP; lia); rewrite unsigned_lit in ERR4 by (unfold ATP; lia); exact ERR4|]. split; [exact AUX4|].
    split.
    { unfold blocks_EXT. cbn [app]. eapply Permutation_trans; [| exact PERM2].
      eapply Permutation_trans; [apply Permutation_middle|]. apply Permutation_app_head. eapply (alb_remove_perm H HH); [exact HEAP2| exact HIN2]. }
    split; [exact HEAP4|].
    split.
    { eapply xpres_trans; [| eapply xpres_trans; [| exact XP4]].
      - eapply (xpres_weaken H); [exact XP1| lia| intros b Hb; apply SUB2; eapply SUBL; exact Hb| auto].
      - eapply (xpres_weaken H); [exact XP2| lia| intros b Hb; eapply SUBL; exact Hb| auto]. }
    split; [exact IM4|]. split; [exact GM4|].
    split; [eapply GOT_echfree_xpres; [exact XP4| exact CSP0| constructor| exact GG2]|].
    unfold ext_cost, EXT_SIZE in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma apopfree_exts_spec : popfree_exts_stmt H.
  Proof. unfold popfree_exts_stmt. apply (askpopfree_spec H HH). Qed.
End W.
