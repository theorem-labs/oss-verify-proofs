From Stdlib Require Import ZArith List Lia Bool Arith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct pj_get_c pj_get_str_c.
Import ListNotations.
Open Scope Z_scope.

Lemma gs_sx32 : forall v, 0 <= v < 2 ^ 31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. rewrite unsigned_lit by lia. f_equal.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296.
  change (4294967296 / 2) with 2147483648. rewrite Z.mod_small by lia. lia.
Qed.

Lemma gs_rd : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. rewrite <- (Z.add_0_r a) at 1.
  rewrite (bytes_at_read rsegs m a bs 0 (length bs) H) by lia.
  cbn [Z.to_nat skipn]. rewrite firstn_all. reflexivity.
Qed.

Lemma gs_rd64 : forall m a v, pj_u64 rsegs m a v -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 (Z_to_bv 64 v)).
Proof. intros m a v (_ & H). pose proof (gs_rd m a _ H) as R. rewrite length_le8 in R. exact R. Qed.

Lemma gs_rd32 : forall m a v, pj_u32 rsegs m a v -> ov_read_bytes rsegs m (wa a) 4 = Some (le4 (Z_to_bv 64 v)).
Proof. intros m a v (_ & H). pose proof (gs_rd m a _ H) as R. rewrite length_le4 in R. exact R. Qed.

Lemma gs_cb_munch : forall W m m' a s, pj_cbytes rsegs m a s -> munch W m m' ->
  disjoint_from W a (Z.of_nat (length s) + 1) -> pj_cbytes rsegs m' a s.
Proof.
  intros W m m' a s (HF & HB) MU HD. split; [exact HF|].
  eapply bytes_at_transport; [exact HB | exact MU |]. rewrite length_map, length_app. cbn [length].
  replace (Z.of_nat (length s + 1)) with (Z.of_nat (length s) + 1) by lia. exact HD.
Qed.

Lemma gs_node_hdr : forall m lblk p t D, pj_node rsegs m lblk p t D ->
  NoDup D /\ pj_apart D p /\ exists num str kids keys n cap, pj_hdr rsegs m p (tag t) num str kids keys n cap.
Proof.
  intros m lblk p t D H. destruct t; cbn [pj_node] in H;
    destruct H as (ND & AP & num & str & kids & keys & n & cap & HH & _);
    (split; [exact ND|]); (split; [exact AP|]); exists num, str, kids, keys, n, cap; exact HH.
Qed.

Lemma gs_items_blocks : forall (lblk : Z -> Z -> Prop) (P : Z -> jv -> list (Z * Z) -> Prop) l a D,
  (forall a' u D1, In u l -> P a' u D1 -> forall x k, In (x, k) D1 -> lblk x k) ->
  pj_items P a l D -> forall x k, In (x, k) D -> lblk x k.
Proof.
  intros lblk P l. induction l as [|u l IH]; intros a D HP H x k Hin; cbn [pj_items] in H.
  - subst D. destruct Hin.
  - destruct H as (D1 & D2 & -> & HPu & Hr). apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    + exact (HP a u D1 (or_introl eq_refl) HPu x k Hin).
    + apply (IH (a + 56) D2); [|exact Hr|exact Hin]. intros a' u' D1' Hu. apply HP. right. exact Hu.
Qed.

Lemma gs_mems_blocks : forall m (lblk : Z -> Z -> Prop) (P : Z -> jv -> list (Z * Z) -> Prop) l a ka D,
  (forall a' nm u D1, In (nm, u) l -> P a' u D1 -> forall x k, In (x, k) D1 -> lblk x k) ->
  pj_mems rsegs m lblk P a ka l D -> forall x k, In (x, k) D -> lblk x k.
Proof.
  intros m lblk P l. induction l as [|[nm u] l IH]; intros a ka D HP H x k Hin; cbn [pj_mems] in H.
  - subst D. destruct Hin.
  - destruct H as (x0 & k0 & D1 & D2 & -> & _ & (Hl & _) & HPu & Hr).
    destruct Hin as [E|Hin]; [injection E as <- <-; exact Hl|].
    apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    + exact (HP a nm u D1 (or_introl eq_refl) HPu x k Hin).
    + apply (IH (a + 56) (ka + 8) D2); [|exact Hr|exact Hin]. intros a' nm' u' D1' Hu. apply (HP a' nm' u' D1'). right. exact Hu.
Qed.

Lemma gs_node_blocks : forall t m lblk p D, pj_node rsegs m lblk p t D -> forall x k, In (x, k) D -> lblk x k.
Proof.
  intros t. induction t as [| | | txt bits | s | items IH | members IH] using jv_ind'; intros m lblk p D H x k Hin;
    cbn [pj_node] in H; destruct H as (_ & _ & num & str & kids & keys & n & cap & _ & H).
  - destruct H as (_ & _ & _ & _ & _ & ->). destruct Hin.
  - destruct H as (_ & _ & _ & _ & _ & ->). destruct Hin.
  - destruct H as (_ & _ & _ & _ & _ & ->). destruct Hin.
  - destruct H as (_ & _ & _ & _ & _ & k0 & (Hl & _) & ->). destruct Hin as [E|[]]. injection E as <- <-. exact Hl.
  - destruct H as (_ & _ & _ & _ & k0 & (Hl & _) & ->). destruct Hin as [E|[]]. injection E as <- <-. exact Hl.
  - destruct H as (_ & _ & _ & _ & Hc & Di & -> & Hi). apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    + destruct (Z.eqb_spec cap 0) as [C0|C0]; [destruct Hin|].
      destruct Hin as [E|[]]. injection E as <- <-. destruct Hc as [(C1 & _)|(_ & Hl)]; [lia | exact Hl].
    + rewrite Forall_forall in IH.
      apply (gs_items_blocks lblk (pj_node rsegs m lblk) items kids Di); [|exact Hi | exact Hin].
      intros a' u D1 Hu H1. exact (IH u Hu m lblk a' D1 H1).
  - destruct H as (_ & _ & _ & Hc & Di & -> & Hi). apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    + destruct (Z.eqb_spec cap 0) as [C0|C0]; [destruct Hin|].
      destruct Hc as [(C1 & _)|(_ & Hl1 & Hl2)]; [lia|].
      destruct Hin as [E|[E|[]]]; injection E as <- <-; assumption.
    + rewrite Forall_forall in IH.
      apply (gs_mems_blocks m lblk (pj_node rsegs m lblk) members kids keys Di); [|exact Hi | exact Hin].
      intros a' nm u D1 Hu H1. exact (IH (nm, u) Hu m lblk a' D1 H1).
Qed.

Lemma gs_kids_pos : forall m lblk o members D kids i nv,
  pj_node rsegs m lblk o (JObj members) D -> (forall a n, lblk a n -> 0 < a) ->
  pj_u64 rsegs m (o + 24) kids -> nth_error members i = Some nv -> 0 < kids.
Proof.
  intros m lblk o members D kids i nv H HL HK E. cbn [pj_node] in H.
  destruct H as (_ & _ & num & str & kids' & keys & n & cap & HH & _ & Hn & Hc & Hcap & _).
  pose proof HH as (_ & _ & _ & _ & HK' & _).
  pose proof (pj_u64_uniq rsegs m _ _ _ HK HK') as ->.
  assert (Hl : (i < length members)%nat) by (apply nth_error_Some; rewrite E; discriminate).
  destruct Hcap as [(C0 & _)|(_ & Hl1 & _)]; [lia | exact (HL _ _ Hl1)].
Qed.

Local Ltac cur_mem := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => mm end.

Theorem pj_get_str_holds : pj_get_contract -> pj_get_str_contract.
Proof.
  intros HPG. unfold pj_get_str_contract, PJ_GET_STR.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lblk o k kname t D lo E0 E1 HN HK LB SP16 ST LO SD MI.
  subst a0 a1. cbn [disjoint_from] in SD.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ST as (LO0 & _ & _).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  step. step. step.
  let mm := cur_mem in rename mm into m1.
  assert (SPE : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
  assert (HN1 : o = 0 \/ pj_node rsegs m1 lblk o t D).
  { destruct HN as [HN|HN]; [left; exact HN|right].
    pose proof (gs_node_blocks t m lblk o D HN) as BL.
    eapply (pj_node_munch rsegs _ _ _ _ _ _ _ _ HN BL MU).
    intros z [Hz|((a & n') & Hb & Hz)]; cbn [outside]; split; try exact I.
    - lia.
    - destruct (LB a n' (BL a n' Hb)) as (_ & _ & _ & Hd). cbn [disjoint_from] in Hd. unfold pj_holds in Hz. cbn [fst snd] in Hz. lia. }
  assert (HK1 : pj_cbytes rsegs m1 k kname) by (eapply gs_cb_munch; [exact HK | exact MU | cbn [disjoint_from]; lia]).
  assert (LB1 : forall a n, lblk a n -> 0 < a /\ a mod 8 = 0 /\ a + n <= 2 ^ 47 /\
       disjoint_from [(a, a + n)] (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) - 48) 48).
  { intros a n Hl. destruct (LB a n Hl) as (A1 & A2 & A3 & A4). cbn [disjoint_from] in A4 |- *. rewrite SPE.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|exact I]. }
  assert (SP161 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) mod 16 = 0) by (rewrite SPE; Z.div_mod_to_equations; lia).
  assert (ST1 : stk rsegs m1 lo (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)))) by (rewrite SPE; exact ST).
  assert (LO1 : lo <= bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) - 48) by (rewrite SPE; lia).
  assert (SD1 : disjoint_from [(o, o + 56); (k, k + Z.of_nat (length kname) + 1)]
                  (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) - 48) 48) by (rewrite SPE; cbn [disjoint_from]; lia).
  eapply evt_cut; [exact (HPG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lblk o k kname t D lo
                            eq_refl eq_refl HN1 HK1 LB1 SP161 ST1 LO1 SD1 MI) |].
  intros ms' (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> &
              MU2 & WM2 & MI2 & ST2 & HK2 & RES).
  replace (ret_pc (Z_to_bv 64 0x15d54)) with (Z_to_bv 64 0x15d54) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  rewrite SPE in MU2, ST2.
  pose proof (rw_cells_transport rsegs _ _ _ _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add Z.of_nat]; lia)) as FR2.
  clear FR.
  assert (MU3 : munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m2).
  { apply (munch_trans _ _ _ _ MU). refine (munch_weaken _ _ _ _ _ MU2).
    intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (Hx & _). split; [lia | exact I]. }
  pose proof (wmono_trans _ _ _ _ WM WM2) as WM3.
  step. if_cases HR0.
  - step. step. step.
    release_frame FR2 ST2 (bv_unsigned sp).
    apply evt_done. do 16 eexists. split; [reflexivity|].
    split; [exact MU3|]. split; [exact WM3|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact HK2|].
    destruct RES as [(O0 & ->)|(O0 & PN & z & -> & GR)]; [left; split; [exact O0 | reflexivity]|right].
    split; [exact O0|]. split; [exact PN|]. exists z. split; [reflexivity|].
    unfold pj_get_res in GR. unfold pj_get_str_res. destruct t; try exact GR.
    destruct GR as [GR|(i & v & kids & Di & Ei & Hpre & HK24 & Ez & Hv & Hinc)]; [left; exact GR|].
    exfalso.
    pose proof (gs_kids_pos _ _ _ _ _ _ _ _ PN (fun a n Hl => proj1 (LB a n Hl)) HK24 Ei) as KP.
    pose proof (gs_node_hdr _ _ _ _ _ Hv) as (_ & _ & _ & _ & _ & _ & _ & _ & ((_ & (ZL & ZH & _)) & _)).
    zify_cond HR0. Z.div_mod_to_equations. lia.
  - destruct RES as [(O0 & ->)|(O0 & PN & z & -> & GR)]; [vm_compute in HR0; discriminate HR0|].
    unfold pj_get_res in GR.
    destruct t as [| | | txt bits | s | items | members]; try (subst z; vm_compute in HR0; discriminate HR0).
    destruct GR as [(_ & ->)|(i & v & kids & Di & Ei & Hpre & HK24 & Ez & Hv & Hinc)]; [vm_compute in HR0; discriminate HR0|].
    pose proof (gs_node_hdr _ _ _ _ _ Hv) as (_ & _ & num & str & kids' & keys & n & cap & HH).
    pose proof HH as ((_ & (ZL & ZH & _)) & HT & _).
    pose proof (gs_rd32 _ _ _ HT) as RT.
    assert (TG : 0 <= tag v <= 6) by (destruct v; cbn [tag]; lia).
    step. rewrite gs_sx32 by lia. step. step. if_cases HT4.
    + zify_cond HT4. step. step. step. step.
      release_frame FR2 ST2 (bv_unsigned sp).
      apply evt_done. do 16 eexists. split; [reflexivity|].
      split; [exact MU3|]. split; [exact WM3|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact HK2|].
      right. split; [exact O0|]. split; [exact PN|]. exists 0. split; [reflexivity|].
      unfold pj_get_str_res. right. exists i, v, kids. split; [exact Ei|]. split; [exact Hpre|]. split; [exact HK24|].
      destruct v; try reflexivity. cbn [tag] in HT4. lia.
    + zify_cond HT4. destruct v as [| | | txt bits | s | items | members']; cbn [tag] in HT4; try lia.
      pose proof Hv as Hv'. cbn [pj_node] in Hv'.
      destruct Hv' as (_ & _ & num2 & str2 & kids2 & keys2 & n2 & cap2 & HH2 & _ & _ & _ & _ & kk & Hc & ED).
      pose proof HH2 as (_ & _ & _ & HS16 & _).
      pose proof (gs_rd64 _ _ _ HS16) as RS.
      step. step. step. step. step.
      release_frame FR2 ST2 (bv_unsigned sp).
      apply evt_done. do 16 eexists. split; [reflexivity|].
      split; [exact MU3|]. split; [exact WM3|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact HK2|].
      right. split; [exact O0|]. split; [exact PN|]. exists str2. split; [reflexivity|].
      unfold pj_get_str_res. right. exists i, (JStr s), kids. split; [exact Ei|]. split; [exact Hpre|].
      split; [exact HK24|]. split; [rewrite <- Ez; exact HS16|].
      exists kk. split; [exact Hc|]. apply Hinc. rewrite ED. left. reflexivity.
Qed.
