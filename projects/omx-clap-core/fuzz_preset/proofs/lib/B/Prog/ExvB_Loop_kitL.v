(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Old-pin kit 4f18c75d4900 rebind: KIT_RUNs / KT_RUN carry the memnorm keep at the post memory, KIT_CALLs / KIT_EXB_CALL
   exv_room Sc S2 and the memnorm keep (in place of the room_live premise), EXV_PRE one more last conjunct (memnorm). *)
(* Theorem Labs, 2026-10: fuzz_preset, image B, ex_value, segment CL (the items loop): the PROOFS of the loop-only kit
   facts of lib/B/Prog/ExvB_Loop_Stmt.v (ExvLoop's statements; this file proves, never restates them):
   - exvl_kit_exb_of_s (KIT_EXB_OF_S): EXBs + s8 = the frame gives EXB. EXB reads its registers only through getr of
     exv_bregs (wdest_ok and prhex_tree's home through spZ, register 2), so EXB is extensional in exv_bregs
     (exvl_exb_regs).
   - exvl_kit_runs (KIT_RUNs, from ExvOpen's T1 KT_RUN) and exvl_kit_calls (KIT_CALLs, from KIT_EXB_CALL): EXBs's
     witness regs0 goes to regs0' := the new registers with s8 set back to regs0's s8; KIT_RUNs's write set (the
     stack window, in->p, in->differs) lies inside KT_RUN's (the stack window, the FP cells of the cursor).
   - exvl_kit_node / exvl_kit_key / exvl_kit_child (KIT_NODE, KIT_KEY, KIT_CHILD): the parent tree at e_v E from EXB's
     prhex_tree (PRH_Reader.v pj_nodeR / pj_hdrR: +24 kids, +32 keys, +40 n; item i at kids + 56 i, key i at
     keys + 8 i), its blocks Lam blocks (prh_ledger's prh_hblock: a harness block, 16-aligned, base - cf_head a live
     allocator block, by alx_blocks at least 4096 and below alloc_ceiling), the shadow of Lam ranges by ExvB_Open_sh.v
     exv_sh_lam, the root's bounds from its home at the entry (EXV_PRE's tree: a Lam block, a fake frame, or the real
     stack between the entry sp and ly_stk_hi <= 2 ^ 47), the apartness of a kid's footprint and a key string from
     EXV_PRE's footprint clause (both lie in pj_footR (e_v E) (e_D E)).
   Rule 24: proves no function (kind: segment lemma).
   Numerals: 24, 32, 40, 56 (LENGTH: pj node field offsets / node size, PRH_Reader.v pj_hdrR), 8 (LENGTH: a key
   pointer / a word), 16 (LENGTH: harness-block alignment), 4096 (LENGTH: the allocator's low bound, ARx_blocks_law),
   256 (LENGTH: a byte's range), 2 ^ 47, 2 ^ 63, 2 ^ 64 (LENGTH: address-space bounds), 2, 3, 4, 8, 9, 18, 19, 24, 25,
   26 (WORD: register numbers of exv_bregs). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import
ExvB_Stmt ExvB_Loop_kit ExvB_Loop_Stmt ExvB_Open_sh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require ExvB_Open_kt.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

#[local] Existing Instance prh_img_B.

(* membership in exv_bregs *)
Local Ltac inb := unfold exv_bregs; cbn [In]; repeat (first [left; reflexivity | right]).

(* ---- the 8-byte value val_mem reads is unique in [0, 2 ^ 64) ---- *)
Lemma exvl_byte_eq : forall x y, Z_to_bv 8 x = Z_to_bv 8 y -> x mod 256 = y mod 256.
Proof.
intros x y H. apply (f_equal bv_unsigned) in H. rewrite !Z_to_bv_unsigned in H. unfold bv_wrap in H.
change (bv_modulus 8) with 256 in H. exact H.
Qed.

Lemma exvl_val8_det : forall (m : word -> option byte) a v v',
  val_mem rsegs m a 8 v -> val_mem rsegs m a 8 v' -> 0 <= v < 2 ^ 64 -> 0 <= v' < 2 ^ 64 -> v = v'.
Proof.
intros m a v v' Hv Hv' Hr Hr'.
assert (BY : forall k, (k < 8)%nat -> YG0f.le_byte v 8 k = YG0f.le_byte v' 8 k).
{ intros k Hk. pose proof (Hv k Hk) as E1. rewrite (Hv' k Hk) in E1.
  assert (E2 : Z_to_bv 8 (YG0f.le_byte v' 8 k) = Z_to_bv 8 (YG0f.le_byte v 8 k)) by (injection E1 as E1; apply bv_eq; exact E1).
  apply exvl_byte_eq in E2. unfold YG0f.le_byte in E2 |- *. rewrite !Z.mod_mod in E2 by lia. symmetry. exact E2. }
rewrite <- (YG0s.le_bytes8 v Hr), <- (YG0s.le_bytes8 v' Hr').
rewrite !BY by lia. reflexivity.
Qed.

(* ---- nth extraction from the item / member lists of the representation ---- *)
Lemma exvl_items_nth : forall (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a D i,
  PRH_Reader.pj_itemsR P a l D -> (i < length l)%nat ->
  exists D1, incl D1 D /\ P (a + 56 * Z.of_nat i) (nth i l PjTree.JNull) D1.
Proof.
intros P l. induction l as [|u l IH]; intros a D i H Hi; cbn [PRH_Reader.pj_itemsR length] in H, Hi; [lia|].
destruct H as (D1 & D2 & -> & H1 & H2). destruct i as [|i].
- exists D1. split; [intros y Hy; apply in_or_app; left; exact Hy|].
  replace (a + 56 * Z.of_nat 0) with a by lia. exact H1.
- destruct (IH (a + 56) D2 i H2 ltac:(lia)) as (D3 & Hinc & H3). exists D3. cbn [nth].
  split; [intros y Hy; apply in_or_app; right; exact (Hinc y Hy)|].
  replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) by lia. exact H3.
Qed.

Lemma exvl_mems_nth : forall m lblk (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a ka D i,
  PRH_Reader.pj_memsR rsegs m lblk P a ka l D -> (i < length l)%nat ->
  exists x k D1, In (x, k) D /\ incl D1 D /\ PRH_Reader.rd_u64 rsegs m (ka + 8 * Z.of_nat i) x /\
    PRH_Reader.pj_cstrR rsegs m lblk x k (fst (nth i l ([], PjTree.JNull))) /\
    P (a + 56 * Z.of_nat i) (snd (nth i l ([], PjTree.JNull))) D1.
Proof.
intros m lblk P l. induction l as [|[nm u] l IH]; intros a ka D i H Hi;
  cbn [PRH_Reader.pj_memsR length] in H, Hi; [lia|].
destruct H as (x & k & D1 & D2 & -> & Hx & Hc & H1 & H2). destruct i as [|i].
- exists x, k, D1. cbn [nth fst snd]. split; [left; reflexivity|].
  split; [intros y Hy; right; apply in_or_app; left; exact Hy|].
  replace (ka + 8 * Z.of_nat 0) with ka by lia. replace (a + 56 * Z.of_nat 0) with a by lia.
  split; [exact Hx|]. split; [exact Hc | exact H1].
- destruct (IH (a + 56) (ka + 8) D2 i H2 ltac:(lia)) as (x' & k' & D3 & Hin & Hinc & Hx' & Hc' & H3).
  exists x', k', D3. cbn [nth]. split; [right; apply in_or_app; right; exact Hin|].
  split; [intros y Hy; right; apply in_or_app; right; exact (Hinc y Hy)|].
  replace (ka + 8 * Z.of_nat (S i)) with (ka + 8 + 8 * Z.of_nat i) by lia.
  replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) by lia.
  split; [exact Hx'|]. split; [exact Hc' | exact H3].
Qed.

(* ---- the node at v: its header (count = exv_count), its kid i, its key i ---- *)
Lemma exvl_node_hdr : forall m lblk v t D,
  PRH_Reader.pj_nodeR rsegs m lblk v t D ->
  exists num str kids keys cap,
    PRH_Reader.pj_hdrR rsegs m v (PjTree.tag t) num str kids keys (Z.of_nat (exv_count t)) cap /\
    ((0 < exv_count t)%nat -> 0 < cap /\ Z.of_nat (exv_count t) <= cap /\ lblk kids (56 * cap)).
Proof.
intros m lblk v t D H.
destruct t as [| | | txt bits | s | items | members]; cbn [PRH_Reader.pj_nodeR] in H;
  destruct H as (_ & _ & num & str & kids & keys & n & cap & Hh & H); exists num, str, kids, keys, cap;
  cbn [exv_count].
- destruct H as (_ & _ & _ & -> & _). split; [exact Hh | intros Hc; lia].
- destruct H as (_ & _ & _ & -> & _). split; [exact Hh | intros Hc; lia].
- destruct H as (_ & _ & _ & -> & _). split; [exact Hh | intros Hc; lia].
- destruct H as (_ & _ & _ & -> & _). split; [exact Hh | intros Hc; lia].
- destruct H as (_ & _ & -> & _). split; [exact Hh | intros Hc; lia].
- destruct H as (_ & _ & -> & Hncap & Hc & _). split; [exact Hh|].
  intros Hc0. destruct Hc as [(Hc1 & _)|(Hcp & Hl)]; [lia|]. split; [exact Hcp|]. split; [exact Hncap | exact Hl].
- destruct H as (_ & -> & Hncap & Hc & _). split; [exact Hh|].
  intros Hc0. destruct Hc as [(Hc1 & _)|(Hcp & Hl & _)]; [lia|]. split; [exact Hcp|]. split; [exact Hncap | exact Hl].
Qed.

Lemma exvl_node_kid : forall m lblk v t D i,
  PRH_Reader.pj_nodeR rsegs m lblk v t D -> (i < exv_count t)%nat ->
  exists kids cap Dk,
    PRH_Reader.rd_u64 rsegs m (v + 24) kids /\ 0 < cap /\ Z.of_nat (exv_count t) <= cap /\ lblk kids (56 * cap) /\
    In (kids, 56 * cap) D /\ incl Dk D /\
    PRH_Reader.pj_nodeR rsegs m lblk (kids + 56 * Z.of_nat i) (exv_kidt t i) Dk.
Proof.
intros m lblk v t D i H Hi.
destruct t as [| | | txt bits | s | items | members]; cbn [exv_count] in Hi |- *; try lia;
  cbn [PRH_Reader.pj_nodeR] in H; destruct H as (_ & _ & num & str & kids & keys & n & cap & Hh & H);
  destruct Hh as (_ & _ & _ & _ & Hk & _).
- destruct H as (_ & _ & -> & Hncap & Hc & Di & -> & Hit).
  destruct Hc as [(Hc0 & _)|(Hcp & Hl)]; [lia|].
  rewrite (proj2 (Z.eqb_neq cap 0) ltac:(lia)). cbn [app].
  destruct (exvl_items_nth _ _ _ _ i Hit Hi) as (D1 & Hinc & H1).
  exists kids, cap, D1. split; [exact Hk|]. split; [exact Hcp|]. split; [exact Hncap|]. split; [exact Hl|].
  split; [left; reflexivity|]. split; [intros y Hy; right; exact (Hinc y Hy)|]. exact H1.
- destruct H as (_ & -> & Hncap & Hc & Di & -> & Hm).
  destruct Hc as [(Hc0 & _)|(Hcp & Hl1 & Hl2)]; [lia|].
  rewrite (proj2 (Z.eqb_neq cap 0) ltac:(lia)). cbn [app].
  destruct (exvl_mems_nth _ _ _ _ _ _ _ i Hm Hi) as (x & k & D1 & _ & Hinc & _ & _ & H1).
  exists kids, cap, D1. split; [exact Hk|]. split; [exact Hcp|]. split; [exact Hncap|]. split; [exact Hl1|].
  split; [left; reflexivity|]. split; [intros y Hy; right; right; exact (Hinc y Hy)|]. exact H1.
Qed.

Lemma exvl_node_key : forall m lblk v ms D i,
  PRH_Reader.pj_nodeR rsegs m lblk v (PjTree.JObj ms) D -> (i < length ms)%nat ->
  exists keys cap x k,
    PRH_Reader.rd_u64 rsegs m (v + 32) keys /\ 0 < cap /\ Z.of_nat (length ms) <= cap /\ lblk keys (8 * cap) /\
    In (x, k) D /\ PRH_Reader.rd_u64 rsegs m (keys + 8 * Z.of_nat i) x /\
    PRH_Reader.pj_cstrR rsegs m lblk x k (fst (nth i ms ([], PjTree.JNull))).
Proof.
intros m lblk v ms D i H Hi.
cbn [PRH_Reader.pj_nodeR] in H. destruct H as (_ & _ & num & str & kids & keys & n & cap & Hh & H).
destruct Hh as (_ & _ & _ & _ & _ & Hk & _).
destruct H as (_ & -> & Hncap & Hc & Di & -> & Hm).
destruct Hc as [(Hc0 & _)|(Hcp & Hl1 & Hl2)]; [lia|].
rewrite (proj2 (Z.eqb_neq cap 0) ltac:(lia)). cbn [app].
destruct (exvl_mems_nth _ _ _ _ _ _ _ i Hm Hi) as (x & k & D1 & Hin & _ & Hx & Hc & _).
exists keys, cap, x, k. split; [exact Hk|]. split; [exact Hcp|]. split; [exact Hncap|]. split; [exact Hl2|].
split; [right; right; exact Hin|]. split; [exact Hx | exact Hc].
Qed.

Section x. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis HYP : EXV_HYP B ARx SK.

(* ---- EXB is extensional in the registers it reads ---- *)
Lemma exvl_exb_regs : forall (fx : YK11.FPState) E lyc Sc Hpc (Wc : world rsegs) (regs regs' : bvmap 5 word)
    memc mdc k pos,
  EXB (fx := fx) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  (forall r, In r exv_bregs -> getr regs' r = getr regs r) ->
  EXB (fx := fx) B ARx SK E lyc Sc Hpc Wc regs' memc mdc k pos.
Proof.
intros fx E lyc Sc Hpc Wc regs regs' memc mdc k pos HB G.
assert (SP : spZ regs' = spZ regs) by (unfold spZ; rewrite (G 2%bv) by inb; reflexivity).
unfold EXB in HB |- *. cbv zeta in HB |- *.
destruct HB as (HJ & HWIN & HFR & HFZ & HHp & HAB & HRM & HLED & HCNT & R2 & R8 & R9 & R18 & R24 & R25 & R26 & R19
  & R3 & R4 & HSV & H176 & HFL & HSRC & HTB & HWD & HSB & HQR & HTREE).
rewrite (G 2%bv), (G 8%bv), (G 9%bv), (G 18%bv), (G 24%bv), (G 25%bv), (G 26%bv), (G 19%bv), (G 3%bv), (G 4%bv)
  by inb.
split; [exact HJ|]. split; [exact HWIN|]. split; [exact HFR|]. split; [exact HFZ|]. split; [exact HHp|].
split; [exact HAB|]. split; [exact HRM|]. split; [exact HLED|]. split; [exact HCNT|].
split; [exact R2|]. split; [exact R8|]. split; [exact R9|]. split; [exact R18|]. split; [exact R24|].
split; [exact R25|]. split; [exact R26|]. split; [exact R19|]. split; [exact R3|]. split; [exact R4|].
split; [exact HSV|]. split; [exact H176|]. split; [exact HFL|]. split; [exact HSRC|]. split; [exact HTB|].
split; [unfold wdest_ok in HWD |- *; rewrite SP; exact HWD|].
split; [exact HSB|]. split; [exact HQR|].
destruct HTREE as [Hv|HT]; [left; exact Hv|right]. unfold prhex_tree, prhex_home in HT |- *. rewrite SP. exact HT.
Qed.

(* KIT_EXB_OF_S *)
Lemma exvl_kit_exb_of_s : forall fx : YK11.FPState, KIT_EXB_OF_S (fx := fx) B ARx SK.
Proof using HYP.
intros fx E lyc Sc Hpc Wc regs memc mdc k pos (regs0 & HB & HR) H24.
apply (exvl_exb_regs fx E lyc Sc Hpc Wc regs0 regs memc mdc k pos HB).
intros r _. destruct (bv_eq_dec _ r 24%bv) as [->|Hne]; [|exact (HR r Hne)].
rewrite H24. pose proof HB as HB'. unfold EXB in HB'. cbv zeta in HB'.
destruct HB' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R24 & _). symmetry. exact R24.
Qed.

(* KIT_RUNs from ExvOpen's T1 (KT_RUN, ExvB_Open_kt.v exv_kt) *)
Lemma exvl_kit_runs : (forall fx : YK11.FPState, KT_RUN (fx := fx) B ARx SK) ->
  forall fx : YK11.FPState, KIT_RUNs (fx := fx) B ARx SK.
Proof using HYP.
intros KT fx E lyc Sc Hpc Wc regs memc mdc k pos regs' memc' mdc' HPRE (regs0 & HB & HR) HJ HK HG HMN HRG.
exists (YK11.regupd regs' 24%bv (getr regs0 24%bv)). split.
- apply (KT fx E lyc Sc Hpc Wc regs0 memc mdc k pos (YK11.regupd regs' 24%bv (getr regs0 24%bv)) memc' mdc' k
    HPRE HB HJ).
  + intros a Ha H1 H2. apply HK; [exact Ha | exact H1 | |].
    * intros Hq. apply H2. split; [|lia]. exists (e_q E, e_q E + 8).
      split; [unfold exv_FP; right; left; reflexivity | cbn [fst snd]; lia].
    * intros Hq. apply H2. split; [|lia]. exists (e_q E + 32, e_q E + 36).
      split; [unfold exv_FP; right; right; right; left; reflexivity | cbn [fst snd]; lia].
  + exact HG.
  + exact HMN.
  + intros r Hr. destruct (bv_eq_dec _ r 24%bv) as [->|Hne].
    * apply YK11.getr_same. intros X0. discriminate X0.
    * rewrite (YK11.getr_other _ _ _ _ Hne). rewrite (HRG r Hr Hne). exact (HR r Hne).
- intros r Hne. symmetry. apply YK11.getr_other. exact Hne.
Qed.

(* KIT_CALLs from KIT_EXB_CALL *)
Lemma exvl_kit_calls : (forall fx : YK11.FPState, KIT_EXB_CALL (fx := fx) B ARx SK) ->
  forall fx : YK11.FPState, KIT_CALLs (fx := fx) B ARx SK.
Proof using HYP.
intros KC fx E lyc Sc Hpc Wc regs memc mdc k pos fx2 FP1 STK1 ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HPRE
  (regs0 & HB & HR) HFP HJ1 HJ2 HWIN HRG HFR HFZ HRM HMN HHp HAB HLED.
assert (HRG0 : forall r, In r exv_bregs -> getr (YK11.regupd regs2 24%bv (getr regs0 24%bv)) r = getr regs0 r).
{ intros r Hr. destruct (bv_eq_dec _ r 24%bv) as [->|Hne].
  - apply YK11.getr_same. intros X0. discriminate X0.
  - rewrite (YK11.getr_other _ _ _ _ Hne). rewrite (HRG r Hr Hne). exact (HR r Hne). }
destruct (KC fx E lyc Sc Hpc Wc regs0 memc mdc k pos fx2 FP1 STK1 ly2 S2 Hp2 W2
  (YK11.regupd regs2 24%bv (getr regs0 24%bv)) mem2 md2 k1 HPRE HB HFP HJ1 HJ2 HWIN HRG0 HFR HFZ HRM HMN HHp HAB HLED)
  as (HB2 & HK2).
split; [|exact HK2]. exists (YK11.regupd regs2 24%bv (getr regs0 24%bv)). split; [exact HB2|].
intros r Hne. symmetry. apply YK11.getr_other. exact Hne.
Qed.

(* ---- the tree: Lam blocks and homes ---- *)
Lemma exvl_lam_rng : forall ly S Hp (W : world rsegs) mem md Lam peak cnt fail ran most own b k,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> In (b, k) Lam ->
  4096 <= b /\ b + k <= alloc_ceiling /\ b mod 16 = 0.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own b k HAR HLED Hin.
pose proof (eh_laws B ARx SK HYP) as LAWS. pose proof (@cf_head_nonneg cp) as CH0.
pose proof HLED as (_ & _ & HB & _). rewrite Forall_forall in HB.
destruct (HB (b, k) Hin) as (Hk0 & Hblk & _ & Hmod & _). cbn [fst snd] in *.
destruct (alx_blocks rsegs B ARx LAWS _ _ _ _ _ _ _ _ HAR Hblk) as (_ & H4096 & Hc & _).
assert (Hrq : k + cf_head <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
split; [lia|]. split; [lia | exact Hmod].
Qed.

Lemma exvl_home_rng : forall ly S Hp (W : world rsegs) mem md Lam peak cnt fail ran most own (regs : bvmap 5 word) p n,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhex_home ly S Lam regs p n -> 4096 <= spZ regs -> ly_stk_hi ly <= 2 ^ 47 ->
  4096 <= p /\ p + n <= 2 ^ 47.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own regs p n HAR HLED Hh Hsp Hhi.
pose proof (eh_laws B ARx SK HYP) as LAWS. pose proof asan_consts as (C1 & _).
destruct Hh as [(b & k & Hin & H1 & H2) | [(cid & pos & Hin & H1 & H2) | (H1 & H2)]].
- destruct (exvl_lam_rng _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HLED Hin) as (L1 & L2 & _). lia.
- destruct (frames_bounds_x rsegs B ARx LAWS _ _ _ _ _ _ cid pos HAR Hin) as (F1 & F2 & _). lia.
- lia.
Qed.

(* KIT_NODE *)
Lemma exvl_kit_node : forall fx : YK11.FPState, KIT_NODE (fx := fx) B ARx SK.
Proof using HYP.
intros fx E lyc Sc Hpc Wc regs memc mdc k pos HPRE (regs0 & HB & _) Hv.
pose proof asan_consts as (C1 & _).
unfold EXV_PRE in HPRE. cbv zeta in HPRE.
destruct HPRE as (HFP & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hv0 & HLED0
  & _).
destruct HFP as ((HAR0 & _ & _ & _ & _ & Hastk & _) & _).
destruct Hastk as (_ & Hstk0 & Hceil & Hslo & _ & H47 & _).
destruct Hv0 as [Hv0|((_ & Hhome0 & _) & _ & _)]; [exfalso; exact (Hv Hv0)|].
destruct (exvl_home_rng _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR0 HLED0 Hhome0 ltac:(lia) H47) as (P1 & P2).
unfold EXB in HB. cbv zeta in HB.
destruct HB as (HJ & _ & _ & _ & _ & _ & _ & HLED & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & _ & HTREE).
destruct HTREE as [Hv1|(Hnd & _ & Hra & _)]; [exfalso; exact (Hv Hv1)|].
pose proof (proj1 HJ) as HAR. cbv beta in HAR.
destruct (exvl_node_hdr _ _ _ _ _ Hnd) as (num & str & kids & keys & cap & Hh & Hc).
destruct Hh as ((Hal & _) & _ & _ & _ & (_ & Hk) & _ & (_ & Hn) & _).
exists kids. split; [exact Hn|]. split; [exact Hk|]. split; [exact Hra|]. split; [exact Hal|].
split; [lia|]. split; [lia|].
intros Hc0. destruct (Hc Hc0) as (Hcap & Hle & Hkl). unfold prh_lin in Hkl.
destruct (exvl_lam_rng _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HLED Hkl) as (L1 & L2 & _). lia.
Qed.

(* KIT_KEY *)
Lemma exvl_kit_key : forall fx : YK11.FPState, KIT_KEY (fx := fx) B ARx SK.
Proof using HYP.
intros fx E lyc Sc Hpc Wc regs memc mdc k pos ms i HPRE (regs0 & HB & _) Hv Et Hi.
unfold EXV_PRE in HPRE. cbv zeta in HPRE.
destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hv0 & _).
destruct Hv0 as [Hv0|(_ & _ & HDJ)]; [exfalso; exact (Hv Hv0)|].
unfold EXB in HB. cbv zeta in HB.
destruct HB as (HJ & _ & _ & _ & _ & _ & _ & HLED & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & _ & HTREE).
destruct HTREE as [Hv1|(Hnd & _ & _ & _)]; [exfalso; exact (Hv Hv1)|].
pose proof (proj1 HJ) as HAR. cbv beta in HAR.
rewrite Et in Hnd.
destruct (exvl_node_key _ _ _ _ _ i Hnd Hi) as (keys & cap & x & kk & (_ & Hkeys) & Hcap & Hlen & Hkl & Hxin
  & (_ & Hx) & (Hxl & Hxk & _ & Hxb)).
unfold prh_lin in Hkl, Hxl.
destruct (exvl_lam_rng _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HLED Hkl) as (K1 & K2 & K3).
exists keys, x, kk.
split; [exact Hkeys|]. split; [lia|]. split; [lia|]. split; [lia|].
split.
{ apply (proj1 (exv_sh_lam B ARx SK HYP lyc Sc Hpc Wc memc mdc (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E)
    keys (8 * cap) (keys + 8 * Z.of_nat i) 8 HAR HLED Hkl ltac:(lia) ltac:(lia) ltac:(lia))). }
split; [exact Hx|]. split; [exact Hxl|]. split; [exact Hxk|]. split; [exact Hxb|].
intros z Hz.
assert (Hf : PRH_Reader.pj_footR (e_v E) (e_D E) z).
{ right. exists (x, kk). split; [exact Hxin|]. unfold PRH_Reader.pj_holdsR. cbn [fst snd]. lia. }
destruct (HDJ z Hf) as (Hs & Hq & Hstk & _).
split; [exact Hstk|]. split; [exact Hs | exact Hq].
Qed.

(* KIT_CHILD *)
Lemma exvl_kit_child : forall fx : YK11.FPState, KIT_CHILD (fx := fx) B ARx SK.
Proof using HYP.
intros fx E lyc Sc Hpc Wc regs memc mdc k pos i kid tk HPRE (regs0 & HB & _) (Hv & Hi & -> & kids0 & Hk0 & Hk0r & ->).
unfold EXV_PRE in HPRE. cbv zeta in HPRE.
destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hv0 & _).
destruct Hv0 as [Hv0|(_ & HF & HDJ)]; [exfalso; exact (Hv Hv0)|].
unfold EXB in HB. cbv zeta in HB.
destruct HB as (HJ & _ & _ & _ & _ & _ & _ & HLED & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & _ & HTREE).
destruct HTREE as [Hv1|(Hnd & _ & _ & _)]; [exfalso; exact (Hv Hv1)|].
pose proof (proj1 HJ) as HAR. cbv beta in HAR.
destruct (exvl_node_kid _ _ _ _ _ i Hnd Hi) as (kids & cap & Dk & (Hkr & Hkv) & Hcap & Hlen & Hkl & Hkin & Hinc & Hkid).
assert (Ek : kids0 = kids) by exact (exvl_val8_det _ _ _ _ Hk0 Hkv Hk0r Hkr).
subst kids0. unfold prh_lin in Hkl.
exists Dk. split; [|split].
- intros regs'. split; [exact Hkid|]. split.
  + left. exists kids, (56 * cap). split; [exact Hkl|]. lia.
  + exact (exv_sh_lam B ARx SK HYP lyc Sc Hpc Wc memc mdc (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E)
      kids (56 * cap) (kids + 56 * Z.of_nat i) 56 HAR HLED Hkl ltac:(lia) ltac:(lia) ltac:(lia)).
- rewrite Forall_forall in HF |- *. intros b Hb. exact (HF b (Hinc b Hb)).
- intros z Hz. apply HDJ. destruct Hz as [Hz|(b & Hb & Hz)].
  + right. exists (kids, 56 * cap). split; [exact Hkin|]. unfold PRH_Reader.pj_holdsR. cbn [fst snd]. lia.
  + right. exists b. split; [exact (Hinc b Hb) | exact Hz].
Qed.
End x.

Print Assumptions exvl_kit_exb_of_s.
Print Assumptions exvl_kit_runs.
Print Assumptions exvl_kit_calls.
Print Assumptions exvl_kit_node.
Print Assumptions exvl_kit_key.
Print Assumptions exvl_kit_child.

(* the instantiation ExvLoop uses: KIT_RUNs from ExvOpen's rebound exv_kt (ExvB_Open_kt.v) *)
Section chk. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis HYP : EXV_HYP B ARx SK.
Check exvl_kit_runs B ARx SK HYP (fun fx => ExvB_Open_kt.exv_kt (fx := fx) B ARx SK HYP).
End chk.
