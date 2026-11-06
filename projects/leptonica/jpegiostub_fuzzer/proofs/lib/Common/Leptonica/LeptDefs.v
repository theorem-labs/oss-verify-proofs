(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition inZ (r : Z * Z) (z : Z) : Prop := fst r <= z < snd r.
Fixpoint inZs (rs : list (Z * Z)) (z : Z) : Prop :=
  match rs with [] => False | r :: t => inZ r z \/ inZs t z end.

(* [comment removed for export] *)
Definition LSTK : Z := 16384.
Lemma LSTK_val : LSTK = 16384. Proof. reflexivity. Qed.

#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma mod16_plus_mod4 : forall p k, p mod 16 = 0 -> k mod 4 = 0 -> (p + k) mod 4 = 0.
Proof.
  intros p k Hp Hk.
  apply Z.mod_divide in Hp; [|lia]. apply Z.mod_divide in Hk; [|lia]. destruct Hp as [a Ha]. destruct Hk as [b Hb].
  subst. replace (a * 16 + b * 4) with ((a * 4 + b) * 4) by lia. apply Z_mod_mult.
Qed.
Lemma mod16_plus_mod8 : forall p k, p mod 16 = 0 -> k mod 8 = 0 -> (p + k) mod 8 = 0.
Proof.
  intros p k Hp Hk.
  apply Z.mod_divide in Hp; [|lia]. apply Z.mod_divide in Hk; [|lia]. destruct Hp as [a Ha]. destruct Hk as [b Hb].
  subst. replace (a * 16 + b * 8) with ((a * 2 + b) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma mod16_plus_mod16 : forall p k, p mod 16 = 0 -> k mod 16 = 0 -> (p + k) mod 16 = 0.
Proof.
  intros p k Hp Hk.
  apply Z.mod_divide in Hp; [|lia]. apply Z.mod_divide in Hk; [|lia]. destruct Hp as [a Ha]. destruct Hk as [b Hb].
  subst. replace (a * 16 + b * 16) with ((a + b) * 16) by lia. apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
Class LeptLayout := {
  ll_hcell : Z;            (* [comment removed for export] *)
  ll_devnull : Z;          (* [comment removed for export] *)
  ll_clr : list (Z * Z);   (* [comment removed for export] *)
  ll_ro : Z * Z;           (* [comment removed for export] *)
  ll_img : Z * Z;          (* [comment removed for export] *)
  ll_lg : Z * Z;           (* [comment removed for export] *)
  ll_ag : Z * Z;           (* [comment removed for export] *)
  ll_errno : Z * Z         (* [comment removed for export] *)
}.

(* [comment removed for export] *)
#[export] Existing Instance aic_base.

Section Defs.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {AIC : AllocCalloc} {LL : LeptLayout}.

(* [comment removed for export] *)
Class LeptPins := {
  pin_env_ro : forall sp0 argv envp M (a : word), al_env sp0 argv envp M -> inZ ll_ro (u a) -> M a = None;
  pin_env_frame : forall sp0 argv envp M M',
      al_env sp0 argv envp M ->
      (forall a : word, inZ ll_ro (u a) \/ inZs ll_clr (u a) \/ (inZ ll_lg (u a) /\ ~ inZ ll_errno (u a)) \/ u sp0 <= u a ->
                        M' a = M a) ->
      al_env sp0 argv envp M';
  pin_glob : forall a, al_globals a -> inZ ll_ag (u a);
  pin_errno : forall a, al_errno_slot a -> inZ ll_errno (u a);
  pin_grant : forall a, al_grantable a -> ~ inZ ll_img (u a) /\ 4096 <= u a;
  pin_inro : forall a, al_in_ro a -> inZ ll_img (u a);
  pin_inrw : forall a, al_in_rw a -> inZ ll_img (u a);
  pin_ret : forall r, ret_ok r -> al_ret_ok r;
  pin_imghi : al_image_hi = snd ll_img;
  pin_lg_ag : forall z, inZ ll_lg z -> ~ inZ ll_ag z;
  pin_ro_below : snd ll_ro <= ll_hcell /\ snd ll_ro <= fst ll_lg /\ snd ll_ro <= fst ll_ag /\ snd ll_ro <= fst ll_errno;
  (* [comment removed for export] *)
  pin_img64 : 0 <= fst ll_img <= snd ll_img /\ snd ll_img <= 2 ^ 40;
  pin_ro_img : fst ll_img <= fst ll_ro /\ snd ll_ro <= snd ll_img;
  pin_lg_img : fst ll_img <= fst ll_lg /\ snd ll_lg <= snd ll_img;
  pin_ag_img : fst ll_img <= fst ll_ag /\ snd ll_ag <= snd ll_img;
  pin_errno_img : fst ll_img <= fst ll_errno /\ snd ll_errno <= snd ll_img;
  pin_clr_img : forall z, inZs ll_clr z -> inZ ll_img z /\ ~ inZ ll_lg z /\ ~ inZ ll_ag z /\ ~ inZ ll_errno z
                          /\ ~ (ll_hcell <= z < ll_hcell + 8);
  pin_hcell : fst ll_img <= ll_hcell /\ ll_hcell + 8 <= snd ll_img /\
              (forall z, ll_hcell <= z < ll_hcell + 8 -> ~ inZ ll_ro z /\ ~ inZ ll_lg z /\ ~ inZ ll_ag z /\ ~ inZ ll_errno z);
  pin_devnull : 0 <= ll_devnull < 2 ^ 64
}.

Context {PINS : LeptPins}.

(* [comment removed for export] *)
Ltac laypins :=
  let P1 := fresh "PIN" in let P2 := fresh "PIN" in let P3 := fresh "PIN" in let P4 := fresh "PIN" in
  let P5 := fresh "PIN" in let P6 := fresh "PIN" in let P7 := fresh "PIN" in let P8 := fresh "PIN" in let P9 := fresh "PIN" in
  pose proof pin_img64 as P1; pose proof pin_ro_img as P2; pose proof pin_lg_img as P3; pose proof pin_ag_img as P4;
  pose proof pin_errno_img as P5; pose proof (proj1 pin_hcell) as P6; pose proof (proj1 (proj2 pin_hcell)) as P7;
  let P10 := fresh "PIN" in pose proof pin_devnull as P8; pose proof LSTK_val as P9; pose proof pin_ro_below as P10.

(* [comment removed for export] *)
Record lctx := LCTX {
  c_sp0 : word; c_argv : list (list byte); c_envp : list (list byte);
  c_top : Z;                     (* [comment removed for export] *)
  c_vm : VmMaps;                 (* [comment removed for export] *)
  c_m0 : word -> option byte;    (* [comment removed for export] *)
  c_A0 : AS                      (* [comment removed for export] *)
}.

Definition win (C : lctx) (a : word) : Prop := c_top C - LSTK <= u a < c_top C.
Definition heap_gap (C : lctx) (a : word) : Prop := al_grantable a /\ u a < alloc_top (c_vm C).
Definition hcell (a : word) : Prop := ll_hcell <= u a < ll_hcell + 8.
Definition scratch (C : lctx) (s : Z) (a : word) : Prop := c_top C - LSTK <= u a < s.

(* [comment removed for export] *)
Definition FRM (C : lctx) (s : Z) (m m' : word -> option byte) : Prop :=
  forall a : word, ~ heap_gap C a -> ~ al_globals a -> ~ al_errno_slot a -> ~ hcell a -> ~ scratch C s a ->
                   m' a = m a.
(* [comment removed for export] *)
Definition DEFK (C : lctx) (m m' : word -> option byte) : Prop :=
  forall a : word, m a <> None -> u a < al_image_hi \/ heap_gap C a \/ m' a <> None.

Record Cok (C : lctx) : Prop := COK {
  ck_top : alloc_top (c_vm C) + 8192 + LSTK <= c_top C;
  ck_sp0 : c_top C <= u (c_sp0 C);
  ck_sp0hi : u (c_sp0 C) <= 0x800000000000;
  ck_al : c_top C mod 16 = 0;
  ck_img : snd ll_img <= alloc_top (c_vm C)
}.

Record W (C : lctx) (A : AS) (m : word -> option byte) (md : Model) : Prop := MKW {
  w_inv : ainv A m (m_vmmaps md);
  w_pure : md_pure md;
  w_env : al_env (c_sp0 C) (c_argv C) (c_envp C) m;
  w_vm : vm_limit (m_vmmaps md) = vm_limit (c_vm C) /\ alloc_top (m_vmmaps md) = alloc_top (c_vm C) /\
         vm_init_sp (m_vmmaps md) = vm_init_sp (c_vm C) /\ vm_reserved (m_vmmaps md) = vm_reserved (c_vm C);
  w_win : forall a, win C a -> m a <> None;
  w_clr : forall a, inZs ll_clr (u a) -> m a = None;
  w_hdl : rdn al_segs m (Z_to_bv 64 ll_hcell) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 ll_devnull));
  w_frm : FRM C (c_top C) (c_m0 C) m;
  w_keep : forall q k, live (c_A0 C) q = Some k -> live A q = Some k;
  w_live0 : forall q k i, live (c_A0 C) q = Some k -> 0 <= i < k -> m (at_ q i) = c_m0 C (at_ q i);
  w_def : DEFK C (c_m0 C) m
}.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma omem_eq_dec : forall (x y : option byte), {x = y} + {x <> y}.
Proof. intros x y. decide equality. apply bv_eq_dec. Defined.

Lemma inZ_dec : forall r z, {inZ r z} + {~ inZ r z}.
Proof.
  intros [lo hi] z. unfold inZ. cbn. destruct (Z_le_gt_dec lo z); [destruct (Z_lt_ge_dec z hi)|]; [left; lia | right; lia | right; lia].
Qed.

Lemma W_ro : forall C A m md a, W C A m md -> inZ ll_ro (u a) -> m a = None.
Proof. intros C A m md a HW Ha. exact (pin_env_ro _ _ _ _ a (w_env _ _ _ _ HW) Ha). Qed.

(* [comment removed for export] *)
Lemma win_facts : forall C a, Cok C -> win C a ->
  ~ inZ ll_img (u a) /\ alloc_top (c_vm C) <= u a /\ ~ al_globals a /\ ~ al_errno_slot a /\ ~ hcell a /\ ~ al_in_ro a /\ ~ al_in_rw a.
Proof.
  intros C a CK Hw. destruct CK. unfold win in Hw. pose proof pin_ag_img. pose proof pin_errno_img. pose proof pin_hcell.
  assert (Himg : ~ inZ ll_img (u a)) by (unfold inZ; lia).
  split; [exact Himg|]. split; [lia|].
  split; [intros G; apply pin_glob in G; unfold inZ in *; lia|].
  split; [intros G; apply pin_errno in G; unfold inZ in *; lia|].
  split; [unfold hcell; lia|].
  split; [intros G; apply pin_inro in G; exact (Himg G)|].
  intros G; apply pin_inrw in G; exact (Himg G).
Qed.

Lemma above_not_gap : forall C a, alloc_top (c_vm C) <= u a -> ~ heap_gap C a.
Proof. intros C a H [_ G]. lia. Qed.

Lemma img_not_gap : forall C a, inZ ll_img (u a) -> ~ heap_gap C a.
Proof. intros C a H [G _]. exact (proj1 (pin_grant a G) H). Qed.

Lemma W_not_owned : forall C A m md a, Cok C -> W C A m md ->
  ~ heap_gap C a -> ~ al_globals a -> ~ owned A a.
Proof.
  intros C A m md a CK HW Hg Hng Ho.
  destruct (ai_owned_where A m (m_vmmaps md) a (w_inv _ _ _ _ HW) Ho) as [G|[[G1 G2] _]]; [exact (Hng G)|].
  apply Hg. split; [exact G1|]. destruct (w_vm _ _ _ _ HW) as (_ & E & _). rewrite <- E. exact G2.
Qed.

Lemma W_win_not_owned : forall C A m md a, Cok C -> W C A m md -> win C a -> ~ owned A a.
Proof.
  intros C A m md a CK HW Hw. destruct (win_facts C a CK Hw) as (_ & Htop & Hng & _).
  apply (W_not_owned C A m md a CK HW); [apply above_not_gap; exact Htop | exact Hng].
Qed.

(* [comment removed for export] *)
Lemma W_call_win : forall C A m md (s K : Z), Cok C -> W C A m md ->
  c_top C - LSTK + K <= s -> s <= c_top C ->
  forall a : word, s - K <= u a < s -> m a <> None /\ ~ owned A a /\ ~ al_in_ro a /\ ~ al_in_rw a.
Proof.
  intros C A m md s K CK HW Hlo Hhi a Ha.
  assert (Hw : win C a) by (unfold win; lia).
  destruct (win_facts C a CK Hw) as (_ & _ & _ & _ & _ & R1 & R2).
  split; [exact (w_win _ _ _ _ HW a Hw)|]. split; [exact (W_win_not_owned C A m md a CK HW Hw)|]. split; assumption.
Qed.

(* [comment removed for export] *)
Lemma FRM_refl : forall C s m, FRM C s m m.
Proof. intros C s m a _ _ _ _ _. reflexivity. Qed.

Lemma FRM_trans : forall C s m1 m2 m3, FRM C s m1 m2 -> FRM C s m2 m3 -> FRM C s m1 m3.
Proof. intros C s m1 m2 m3 A B a H1 H2 H3 H4 H5. rewrite (B a H1 H2 H3 H4 H5). apply A; assumption. Qed.

Lemma FRM_mono : forall C s s' m m', FRM C s m m' -> s <= s' -> FRM C s' m m'.
Proof. intros C s s' m m' F Hs a H1 H2 H3 H4 H5. apply F; try assumption. unfold scratch in *. lia. Qed.

Lemma DEFK_refl : forall C m, DEFK C m m.
Proof. intros C m a H. right; right; exact H. Qed.

Lemma DEFK_trans : forall C m1 m2 m3, DEFK C m1 m2 -> DEFK C m2 m3 -> DEFK C m1 m3.
Proof.
  intros C m1 m2 m3 A B a H. destruct (A a H) as [X|[X|X]]; [left; exact X | right; left; exact X |].
  exact (B a X).
Qed.

(* [comment removed for export] *)
Lemma FRM_rdn_above : forall C s m m' (a : Z) (n : nat), Cok C -> FRM C s m m' ->
  s <= a -> a + Z.of_nat n <= 2 ^ 64 -> c_top C - LSTK <= s ->
  rdn al_segs m' (Z_to_bv 64 a) n = rdn al_segs m (Z_to_bv 64 a) n.
Proof.
  intros C s m m' a n CK F Hs Hn Hlo. destruct CK. laypins. destruct n as [|n']; [reflexivity|].
  apply rdn_ext; rewrite u_Z2bv by lia; [lia|].
  intros x Hx. apply F.
  - apply above_not_gap. lia.
  - intros G; apply pin_glob in G; unfold inZ in G; lia.
  - intros G; apply pin_errno in G; unfold inZ in G; lia.
  - unfold hcell; lia.
  - unfold scratch; lia.
Qed.

(* [comment removed for export] *)
Lemma FRM_img_cell : forall C s m m' (a : word), Cok C -> FRM C s m m' ->
  inZ ll_img (u a) -> ~ inZ ll_ag (u a) -> ~ inZ ll_errno (u a) -> ~ hcell a -> m' a = m a.
Proof.
  intros C s m m' a CK F Hi Hag He Hh. destruct CK. apply F.
  - apply img_not_gap. exact Hi.
  - intros G; apply pin_glob in G. exact (Hag G).
  - intros G; apply pin_errno in G. exact (He G).
  - exact Hh.
  - unfold scratch, inZ in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fresh_blk (C : lctx) (A : AS) (a : word) : Prop :=
  exists p n, live A p = Some n /\ live (c_A0 C) p = None /\ u p <= u a < u p + n.

Lemma round16_ge : forall n, 0 <= n -> n <= round16 n.
Proof. intros n Hn. unfold round16. pose proof (Z.div_mod (n + 15) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 15) 16 ltac:(lia)). lia. Qed.

(* [comment removed for export] *)
Lemma blk_byte : forall C A m md p n (a : word), Cok C -> W C A m md -> live A p = Some n -> u p <= u a < u p + n ->
  heap_gap C a /\ m a <> None /\ ~ inZ ll_img (u a) /\ ~ win C a /\ ~ al_globals a.
Proof.
  intros C A m md p n a CK HW L R. pose proof (w_inv _ _ _ _ HW) as Hinv.
  destruct (ai_live_hull A m (m_vmmaps md) p n Hinv L) as (Hn0 & _ & Htop & Hall).
  pose proof (round16_ge n Hn0) as Hr.
  assert (Ea : at_ p (u a - u p) = a) by (unfold at_; apply bv_eq; rewrite u_Z2bv by (pose proof (u64_range a); lia); lia).
  destruct (Hall (u a - u p) ltac:(lia)) as (Ho & Hd & _). rewrite Ea in Ho, Hd.
  pose proof (ai_live_not_globals A m (m_vmmaps md) p n (u a - u p) Hinv L ltac:(lia)) as Hng. rewrite Ea in Hng.
  destruct (ai_owned_where A m (m_vmmaps md) a Hinv Ho) as [G|[[G1 G2] _]]; [exact (False_ind _ (Hng G))|].
  destruct (w_vm _ _ _ _ HW) as (_ & E & _). rewrite E in G2.
  assert (Hgap : heap_gap C a) by (split; assumption).
  split; [exact Hgap|]. split; [exact Hd|]. split; [intros Hi; exact (proj1 (pin_grant a G1) Hi)|].
  split; [|exact Hng]. intros Hw. destruct (win_facts C a CK Hw) as (_ & T & _). lia.
Qed.

(* [comment removed for export] *)
Lemma blk_range : forall C A m md p n, Cok C -> W C A m md -> live A p = Some n -> 0 < n ->
  4096 <= u p /\ u p + n <= alloc_top (c_vm C).
Proof.
  intros C A m md p n CK HW L Hn.
  destruct (blk_byte C A m md p n p CK HW L ltac:(lia)) as ([G1 G2] & _).
  pose proof (ai_live_hull A m (m_vmmaps md) p n (w_inv _ _ _ _ HW) L) as (_ & _ & TOP & _).
  destruct (w_vm _ _ _ _ HW) as (_ & E & _). rewrite E in TOP. pose proof (round16_ge n ltac:(lia)).
  split; [exact (proj2 (pin_grant p G1)) | lia].
Qed.

Lemma W_mod_local : forall C A m m' md, Cok C -> W C A m md ->
  (forall a, m' a <> m a -> win C a \/ fresh_blk C A a) ->
  (forall a, m a <> None -> m' a <> None) ->
  (forall a, m' a <> None -> m a <> None) ->
  W C A m' md.
Proof.
  intros C A m m' md CK HW Hch Hg1 Hg2.
  assert (Heq : forall a, ~ win C a -> ~ fresh_blk C A a -> m' a = m a).
  { intros a H1 H2. destruct (omem_eq_dec (m' a) (m a)) as [E|NE]; [exact E|].
    exfalso. destruct (Hch a NE) as [X|X]; [exact (H1 X)|exact (H2 X)]. }
  pose proof HW as [Hinv Hpure Henv Hvm Hwin Hclr Hhdl Hfrm Hkeep Hlive0 Hdef].
  assert (Himg_nw : forall a, inZ ll_img (u a) -> ~ win C a).
  { intros a Hi Hw. destruct (win_facts C a CK Hw) as (X & _). exact (X Hi). }
  assert (Himg_nf : forall a, inZ ll_img (u a) -> ~ fresh_blk C A a).
  { intros a Hi (p & n & L & _ & R). destruct (blk_byte C A m md p n a CK HW L R) as (_ & _ & X & _). exact (X Hi). }
  laypins.
  assert (Htop_nw : forall a, c_top C <= u a -> ~ win C a) by (intros a Ha Hw; unfold win in Hw; lia).
  assert (Htop_nf : forall a, c_top C <= u a -> ~ fresh_blk C A a).
  { intros a Ha (p & n & L & _ & R). destruct (blk_byte C A m md p n a CK HW L R) as ([_ G] & _). destruct CK. lia. }
  split.
  - (* [comment removed for export] *)
    apply (ai_frame A m m' (m_vmmaps md) Hinv).
    + intros a Ho Hnl. apply Heq.
      * intros Hw. exact (W_win_not_owned C A m md a CK HW Hw Ho).
      * intros (p & n & L & _ & R). exact (Hnl p n L R).
    + intros a _ Hx. exact (Hg1 a Hx).
    + intros a _ Hx. exact (Hg2 a Hx).
  - exact Hpure.
  - apply (pin_env_frame _ _ _ m m' Henv). intros a [Ha|[Ha|[[Ha _]|Ha]]].
    + apply Heq; [apply Himg_nw | apply Himg_nf]; unfold inZ in *; lia.
    + destruct (pin_clr_img (u a) Ha) as (Hi & _). apply Heq; [apply Himg_nw | apply Himg_nf]; exact Hi.
    + apply Heq; [apply Himg_nw | apply Himg_nf]; unfold inZ in *; lia.
    + apply Heq; [apply Htop_nw | apply Htop_nf]; destruct CK; lia.
  - exact Hvm.
  - intros a Hw. apply Hg1. exact (Hwin a Hw).
  - intros a Hc. destruct (pin_clr_img (u a) Hc) as (Hi & _). rewrite Heq; [exact (Hclr a Hc) | apply Himg_nw; exact Hi | apply Himg_nf; exact Hi].
  - rewrite <- Hhdl. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|].
    intros x Hx. cbn in Hx. apply Heq; [apply Himg_nw | apply Himg_nf]; unfold inZ; lia.
  - intros a H1 H2 H3 H4 H5. rewrite Heq; [exact (Hfrm a H1 H2 H3 H4 H5) | |].
    + intros Hw. apply H5. unfold win, scratch in *. lia.
    + intros (p & n & L & _ & R). destruct (blk_byte C A m md p n a CK HW L R) as (G & _). exact (H1 G).
  - exact Hkeep.
  - intros q k i L Hi. pose proof (Hkeep q k L) as L1.
    destruct (ai_live_hull A m (m_vmmaps md) q k Hinv L1) as (Hk0 & _ & Htopq & _). pose proof (round16_ge k Hk0).
    pose proof (alloc_top_lt (m_vmmaps md)) as Tlt. unfold two_pow_64 in Tlt.
    assert (R : u q <= u (at_ q i) < u q + k) by (unfold at_; rewrite u_Z2bv by (pose proof (u64_range q); lia); lia).
    rewrite Heq; [exact (Hlive0 q k i L Hi) | |].
    + destruct (blk_byte C A m md q k (at_ q i) CK HW L1 R) as (_ & _ & _ & X & _). exact X.
    + intros (p & n & Lp & Lp0 & Rp).
      destruct (bv_eq_dec _ p q) as [E|NE]; [subst p; congruence|].
      destruct (ai_live_hull A m (m_vmmaps md) p n Hinv Lp) as (Hn0 & _ & _ & _). pose proof (round16_ge n Hn0).
      pose proof (ai_live_disjoint A m (m_vmmaps md) p n q k Hinv Lp L1 NE) as D. lia.
  - intros a H. destruct (Hdef a H) as [X|[X|X]]; [left; exact X | right; left; exact X | right; right; exact (Hg1 a X)].
Qed.

(* [comment removed for export] *)
Lemma W_store_win : forall C A m md (a : word) bs, Cok C -> W C A m md ->
  c_top C - LSTK <= u a -> u a + Z.of_nat (length bs) <= c_top C ->
  W C A (wbytes m a bs) md.
Proof.
  intros C A m md a bs CK HW Hlo Hhi. pose proof CK as [T1 T2 T3 T4 T5]. laypins.
  assert (Hnw : u a + Z.of_nat (length bs) <= 2 ^ 64) by lia.
  apply (W_mod_local C A m _ md CK HW).
  - intros x Hx. left. unfold win.
    destruct (Z_lt_ge_dec (u x) (u a)); [exfalso; apply Hx; apply wbytes_outside; lia|].
    destruct (Z_lt_ge_dec (u x) (u a + Z.of_nat (length bs))); [lia|].
    exfalso; apply Hx; apply wbytes_outside; lia.
  - intros x Hx. apply wbytes_grows. exact Hx.
  - intros x Hx. destruct (Z_lt_ge_dec (u x) (u a)); [rewrite wbytes_outside in Hx by lia; exact Hx|].
    destruct (Z_lt_ge_dec (u x) (u a + Z.of_nat (length bs))); [|rewrite wbytes_outside in Hx by lia; exact Hx].
    apply (w_win _ _ _ _ HW). unfold win. lia.
Qed.

(* [comment removed for export] *)
Lemma W_store_blk : forall C A m md (p a : word) (n : Z) bs, Cok C -> W C A m md ->
  live A p = Some n -> live (c_A0 C) p = None ->
  u p <= u a -> u a + Z.of_nat (length bs) <= u p + n ->
  W C A (wbytes m a bs) md.
Proof.
  intros C A m md p a n bs CK HW L L0 Hlo Hhi.
  destruct (ai_live_hull A m (m_vmmaps md) p n (w_inv _ _ _ _ HW) L) as (Hn0 & _ & Htop & Hall).
  assert (Hr : n <= round16 n) by (unfold round16; pose proof (Z.div_mod (n + 15) 16 ltac:(lia)); pose proof (Z.mod_pos_bound (n + 15) 16 ltac:(lia)); lia).
  pose proof (alloc_top_lt (m_vmmaps md)) as Tlt. unfold two_pow_64 in Tlt.
  assert (Hnw : u a + Z.of_nat (length bs) <= 2 ^ 64) by lia.
  apply (W_mod_local C A m _ md CK HW).
  - intros x Hx. right. exists p, n. split; [exact L|]. split; [exact L0|].
    destruct (Z_lt_ge_dec (u x) (u a)); [exfalso; apply Hx; apply wbytes_outside; lia|].
    destruct (Z_lt_ge_dec (u x) (u a + Z.of_nat (length bs))); [lia|].
    exfalso; apply Hx; apply wbytes_outside; lia.
  - intros x Hx. apply wbytes_grows. exact Hx.
  - intros x Hx. destruct (Z_lt_ge_dec (u x) (u a)); [rewrite wbytes_outside in Hx by lia; exact Hx|].
    destruct (Z_lt_ge_dec (u x) (u a + Z.of_nat (length bs))); [|rewrite wbytes_outside in Hx by lia; exact Hx].
    destruct (Hall (u x - u p) ltac:(lia)) as (_ & D & _).
    replace (at_ p (u x - u p)) with x in D by (unfold at_; apply bv_eq; rewrite u_Z2bv by (pose proof (u64_range x); lia); lia).
    exact D.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition LIVK (A : AS) (m m' : word -> option byte) : Prop :=
  forall q k i, live A q = Some k -> 0 <= i < k -> m' (at_ q i) = m (at_ q i).
Definition POSTM (C : lctx) (A : AS) (s : Z) (m m' : word -> option byte) : Prop := FRM C s m m' /\ LIVK A m m'.
(* [comment removed for export] *)
Definition sub_live (A A' : AS) : Prop := forall q k, live A q = Some k -> live A' q = Some k.

Lemma sub_live_refl : forall A, sub_live A A. Proof. intros A q k H; exact H. Qed.
Lemma sub_live_trans : forall A1 A2 A3, sub_live A1 A2 -> sub_live A2 A3 -> sub_live A1 A3.
Proof. intros A1 A2 A3 X Y q k H. apply Y, X, H. Qed.
Lemma sub_live_eq : forall A A', (forall q, live A' q = live A q) -> sub_live A A'.
Proof. intros A A' E q k H. rewrite E. exact H. Qed.
Lemma sub_live_new : forall A A' (res : word) n, live A res = None -> live A' res = Some n ->
  (forall q, q <> res -> live A' q = live A q) -> sub_live A A'.
Proof.
  intros A A' res n L0 L1 EQ q k H. destruct (bv_eq_dec _ q res) as [->|NE]; [congruence|]. rewrite (EQ q NE). exact H.
Qed.
Lemma sub_live_new2 : forall A A' (r1 r2 : word) n1 n2, live A r1 = None -> live A r2 = None ->
  live A' r1 = Some n1 -> live A' r2 = Some n2 -> (forall q, q <> r1 -> q <> r2 -> live A' q = live A q) -> sub_live A A'.
Proof.
  intros A A' r1 r2 n1 n2 L1 L2 L1' L2' EQ q k H.
  destruct (bv_eq_dec _ q r1) as [->|N1]; [congruence|]. destruct (bv_eq_dec _ q r2) as [->|N2]; [congruence|].
  rewrite (EQ q N1 N2). exact H.
Qed.
Lemma sub_live_free : forall A A' (p : word), live A p = None -> live A' p = None ->
  (forall q, q <> p -> live A' q = live A q) -> forall A0, sub_live A0 A -> live A0 p = None -> sub_live A0 A'.
Proof.
  intros A A' p _ Lp EQ A0 SUB L0 q k H. destruct (bv_eq_dec _ q p) as [->|NE]; [congruence|]. rewrite (EQ q NE). apply SUB, H.
Qed.

Lemma W_sub0 : forall C A m md, W C A m md -> sub_live (c_A0 C) A.
Proof. intros C A m md HW q k L. exact (w_keep _ _ _ _ HW q k L). Qed.

Lemma LIVK_refl : forall A m, LIVK A m m. Proof. intros A m q k i _ _; reflexivity. Qed.
Lemma LIVK_trans : forall A m1 m2 m3, LIVK A m1 m2 -> LIVK A m2 m3 -> LIVK A m1 m3.
Proof. intros A m1 m2 m3 X Y q k i L Hi. rewrite (Y q k i L Hi). exact (X q k i L Hi). Qed.
Lemma LIVK_sub : forall A A1 m m', sub_live A A1 -> LIVK A1 m m' -> LIVK A m m'.
Proof. intros A A1 m m' S X q k i L Hi. exact (X q k i (S q k L) Hi). Qed.

Lemma POSTM_refl : forall C A s m, POSTM C A s m m.
Proof. intros; split; [apply FRM_refl | apply LIVK_refl]. Qed.
Lemma POSTM_trans : forall C A s m1 m2 m3, POSTM C A s m1 m2 -> POSTM C A s m2 m3 -> POSTM C A s m1 m3.
Proof. intros C A s m1 m2 m3 [F1 L1] [F2 L2]. split; [eapply FRM_trans; eassumption | eapply LIVK_trans; eassumption]. Qed.
Lemma POSTM_sub : forall C A A1 s m m', sub_live A A1 -> POSTM C A1 s m m' -> POSTM C A s m m'.
Proof. intros C A A1 s m m' S [F L]. split; [exact F | eapply LIVK_sub; eassumption]. Qed.
Lemma POSTM_mono : forall C A s s' m m', s <= s' -> POSTM C A s m m' -> POSTM C A s' m m'.
Proof. intros C A s s' m m' Hs [F L]. split; [eapply FRM_mono; eassumption | exact L]. Qed.

(* [comment removed for export] *)
Lemma POSTM_range : forall C A m md m' (lo hi s : Z), Cok C -> W C A m md ->
  (forall a : word, ~ (lo <= u a < hi) -> m' a = m a) -> c_top C - LSTK <= lo -> hi <= s -> s <= c_top C ->
  POSTM C A s m m'.
Proof.
  intros C A m md m' lo hi s CK HW OUT Hlo Hhi Hs. split.
  - intros a _ _ _ _ H5. apply OUT. unfold scratch in H5. lia.
  - intros q k i L Hi. apply OUT. intros R.
    pose proof (ai_live_hull A m (m_vmmaps md) q k (w_inv _ _ _ _ HW) L) as (Hk0 & _ & _ & _).
    assert (RR : u q <= u (at_ q i) < u q + k).
    { unfold at_. pose proof (alloc_top_lt (m_vmmaps md)) as T. unfold two_pow_64 in T.
      pose proof (ai_live_hull A m (m_vmmaps md) q k (w_inv _ _ _ _ HW) L) as (_ & _ & TOP & _). pose proof (round16_ge k Hk0).
      rewrite u_Z2bv by (pose proof (u64_range q); lia). lia. }
    destruct (blk_byte C A m md q k (at_ q i) CK HW L RR) as (_ & _ & _ & NW & _). apply NW. unfold win. lia.
Qed.

Lemma POSTM_wbytes_win : forall C A m md (a : word) bs (s : Z), Cok C -> W C A m md ->
  c_top C - LSTK <= u a -> u a + Z.of_nat (length bs) <= s -> s <= c_top C ->
  POSTM C A s m (wbytes m a bs).
Proof.
  intros C A m md a bs s CK HW Hlo Hhi Hs. laypins. pose proof CK as [T1 T2 T3 T4 T5].
  apply (POSTM_range C A m md _ (u a) (u a + Z.of_nat (length bs)) s CK HW); [|lia|lia|lia].
  intros x Hx. apply wbytes_outside; lia.
Qed.

(* [comment removed for export] *)
Lemma POSTM_blk : forall C A A' m md (p a : word) (n : Z) bs (s : Z), Cok C -> W C A' m md ->
  live A' p = Some n -> live A p = None -> sub_live A A' ->
  u p <= u a -> u a + Z.of_nat (length bs) <= u p + n ->
  POSTM C A s m (wbytes m a bs).
Proof.
  intros C A A' m md p a n bs s CK HW L L0 SUB Hlo Hhi.
  pose proof (ai_live_hull A' m (m_vmmaps md) p n (w_inv _ _ _ _ HW) L) as (Hn0 & _ & TOP & _). pose proof (round16_ge n Hn0).
  pose proof (alloc_top_lt (m_vmmaps md)) as T. unfold two_pow_64 in T.
  split.
  - intros x H1 _ _ _ _. destruct (Z_lt_ge_dec (u x) (u a)); [apply wbytes_outside; lia|].
    destruct (Z_lt_ge_dec (u x) (u a + Z.of_nat (length bs))); [|apply wbytes_outside; lia].
    exfalso. apply H1. destruct (blk_byte C A' m md p n x CK HW L ltac:(lia)) as (G & _). exact G.
  - intros q k i Lq Hi. pose proof (SUB q k Lq) as Lq'.
    assert (NE : p <> q) by (intros ->; congruence).
    pose proof (ai_live_disjoint A' m (m_vmmaps md) p n q k (w_inv _ _ _ _ HW) L Lq' NE) as D.
    pose proof (ai_live_hull A' m (m_vmmaps md) q k (w_inv _ _ _ _ HW) Lq') as (Hk0 & _ & TOPq & _). pose proof (round16_ge k Hk0).
    apply wbytes_outside; [lia|]. unfold at_. rewrite u_Z2bv by (pose proof (u64_range q); lia). lia.
Qed.

(* [comment removed for export] *)
Lemma WP_win : forall C Aw A0 mb m md (a : word) bs (s : Z), Cok C ->
  W C Aw m md /\ POSTM C A0 s mb m -> sub_live A0 Aw ->
  c_top C - LSTK <= u a -> u a + Z.of_nat (length bs) <= s -> s <= c_top C ->
  W C Aw (wbytes m a bs) md /\ POSTM C A0 s mb (wbytes m a bs).
Proof.
  intros C Aw A0 mb m md a bs s CK [HW PM] SUB Hlo Hhi Hs. split.
  - apply (W_store_win C Aw m md a bs CK HW Hlo). lia.
  - eapply POSTM_trans; [exact PM|]. apply (POSTM_sub C A0 Aw _ _ _ SUB). eapply POSTM_wbytes_win; eassumption.
Qed.

Lemma WP_blk : forall C A A' mb m md (p a : word) (n : Z) bs (s : Z), Cok C ->
  W C A' m md /\ POSTM C A s mb m ->
  live A' p = Some n -> live A p = None -> live (c_A0 C) p = None -> sub_live A A' ->
  u p <= u a -> u a + Z.of_nat (length bs) <= u p + n ->
  W C A' (wbytes m a bs) md /\ POSTM C A s mb (wbytes m a bs).
Proof.
  intros C A A' mb m md p a n bs s CK [HW PM] L L0 L00 SUB Hlo Hhi. split.
  - eapply (W_store_blk C A' m md p a n bs CK HW L L00 Hlo Hhi).
  - eapply POSTM_trans; [exact PM|]. eapply (POSTM_blk C A A'); eassumption.
Qed.

(* [comment removed for export] *)
Lemma POSTM_local : forall C Ar A m md m' (s : Z), Cok C -> W C A m md -> sub_live Ar A ->
  (forall a, m' a <> m a -> scratch C s a \/ (exists p n, live A p = Some n /\ live Ar p = None /\ u p <= u a < u p + n)) ->
  POSTM C Ar s m m'.
Proof.
  intros C Ar A m md m' s CK HW SUB CH. split.
  - intros a H1 _ _ _ H5. destruct (omem_eq_dec (m' a) (m a)) as [E|NE]; [exact E|]. exfalso.
    destruct (CH a NE) as [X|(p & n & L & _ & R)]; [exact (H5 X)|].
    destruct (blk_byte C A m md p n a CK HW L R) as (G & _). exact (H1 G).
  - intros q k i Lq Hi. destruct (omem_eq_dec (m' (at_ q i)) (m (at_ q i))) as [E|NE]; [exact E|]. exfalso.
    pose proof (SUB q k Lq) as LqA.
    pose proof (ai_live_hull A m (m_vmmaps md) q k (w_inv _ _ _ _ HW) LqA) as (Hk0 & _ & TOPq & _). pose proof (round16_ge k Hk0).
    pose proof (alloc_top_lt (m_vmmaps md)) as T. unfold two_pow_64 in T.
    assert (R : u q <= u (at_ q i) < u q + k) by (unfold at_; rewrite u_Z2bv by (pose proof (u64_range q); lia); lia).
    destruct (CH _ NE) as [X|(p & n & L & L0 & Rp)].
    + destruct (blk_byte C A m md q k (at_ q i) CK HW LqA R) as ([_ G] & _). unfold scratch in X.
      destruct CK. pose proof LSTK_val. lia.
    + assert (NE' : p <> q) by (intros ->; congruence).
      pose proof (ai_live_disjoint A m (m_vmmaps md) p n q k (w_inv _ _ _ _ HW) L LqA NE') as D.
      pose proof (ai_live_hull A m (m_vmmaps md) p n (w_inv _ _ _ _ HW) L) as (Hn0 & _ & _ & _). pose proof (round16_ge n Hn0). lia.
Qed.

(* [comment removed for export] *)
Lemma W_local : forall C A m md m' (s : Z), Cok C -> W C A m md -> s <= c_top C ->
  (forall a, m' a <> m a -> scratch C s a \/ (exists p n, live A p = Some n /\ live (c_A0 C) p = None /\ u p <= u a < u p + n)) ->
  mem_grows m m' -> W C A m' md.
Proof.
  intros C A m md m' s CK HW Hs CH GR. apply (W_mod_local C A m m' md CK HW).
  - intros a NE. destruct (CH a NE) as [X|(p & n & L & L0 & R)]; [left; unfold win, scratch in *; lia | right; exists p, n; split; [exact L | split; [exact L0 | exact R]]].
  - exact GR.
  - intros a D'. destruct (omem_eq_dec (m' a) (m a)) as [E|NE]; [rewrite <- E; exact D'|].
    destruct (CH a NE) as [X|(p & n & L & L0 & R)].
    + apply (w_win _ _ _ _ HW). unfold win, scratch in *. lia.
    + destruct (blk_byte C A m md p n a CK HW L R) as (_ & D & _). exact D.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma W_after_call : forall C A m md A' m' vm' (s K : Z),
  Cok C -> W C A m md -> 0 <= K -> c_top C - LSTK + K <= s -> s <= c_top C ->
  ainv A' m' vm' ->
  (forall q k, live (c_A0 C) q = Some k -> live A' q = Some k) ->
  (forall a, ~ owned A a -> ~ owned A' a -> ~ al_errno_slot a -> ~ (s - K <= u a < s) -> m' a = m a) ->
  (forall q k i, live (c_A0 C) q = Some k -> 0 <= i < k -> m' (at_ q i) = m (at_ q i)) ->
  (forall a, m a <> None -> u a < al_image_hi \/ owned A a \/ m' a <> None) ->
  vm_limit vm' = vm_limit (m_vmmaps md) -> alloc_top vm' = alloc_top (m_vmmaps md) ->
  vm_init_sp vm' = vm_init_sp (m_vmmaps md) -> vm_reserved vm' = vm_reserved (m_vmmaps md) ->
  W C A' m' (with_vmmaps vm' md) /\ FRM C s m m'.
Proof.
  intros C A m md A' m' vm' s K CK HW HK Hlo Hhi Hinv' Hkeep' Hfr Hlive Hdef E1 E2 E3 E4.
  pose proof HW as [Hinv Hpure Henv Hvm Hwin Hclr Hhdl Hfrm Hkeep Hlive0 Hdef0].
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. pose proof pin_imghi as PIH.
  destruct Hvm as (V1 & V2 & V3 & V4).
  (* [comment removed for export] *)
  assert (Hno' : forall a, ~ heap_gap C a -> ~ al_globals a -> ~ owned A' a).
  { intros a Hg Hng Ho. destruct (ai_owned_where A' m' vm' a Hinv' Ho) as [G|[[G1 G2] _]]; [exact (Hng G)|].
    apply Hg. split; [exact G1|]. rewrite <- V2, <- E2. exact G2. }
  assert (Hno : forall a, ~ heap_gap C a -> ~ al_globals a -> ~ owned A a)
    by (intros a Hg Hng; exact (W_not_owned C A m md a CK HW Hg Hng)).
  (* [comment removed for export] *)
  assert (F : FRM C s m m').
  { intros a H1 H2 H3 H4 H5. apply Hfr; [apply Hno; assumption | apply Hno'; assumption | exact H3 |].
    unfold scratch in H5. lia. }
  assert (Fimg : forall a, inZ ll_img (u a) -> ~ inZ ll_ag (u a) -> ~ inZ ll_errno (u a) -> ~ hcell a -> m' a = m a).
  { intros a Hi Hag He Hh. apply (FRM_img_cell C s m m' a CK F Hi Hag He Hh). }
  split; [|exact F].
  split.
  - rewrite with_vmmaps_vmmaps. exact Hinv'.
  - apply md_pure_with_vmmaps. exact Hpure.
  - apply (pin_env_frame _ _ _ m m' Henv). intros a [Ha|[Ha|[[Ha Hne]|Ha]]].
    + apply Fimg; unfold hcell, inZ in *; lia.
    + destruct (pin_clr_img (u a) Ha) as (Hi & _ & Hag & He & Hh). apply Fimg; [exact Hi | exact Hag | exact He | exact Hh].
    + apply Fimg; [unfold inZ in *; lia | exact (pin_lg_ag _ Ha) | exact Hne |].
      intros G. destruct (proj2 (proj2 pin_hcell) (u a) G) as (_ & X & _). exact (X Ha).
    + apply F.
      * apply above_not_gap. lia.
      * intros G; apply pin_glob in G; unfold inZ in *; lia.
      * intros G; apply pin_errno in G; unfold inZ in *; lia.
      * unfold hcell; lia.
      * unfold scratch; lia.
  - rewrite !with_vmmaps_vmmaps. rewrite E1, E2, E3, E4. repeat split; assumption.
  - intros a Hw. destruct (Hdef a (Hwin a Hw)) as [X|[X|X]]; [| exfalso; exact (W_win_not_owned C A m md a CK HW Hw X) | exact X].
    exfalso. destruct (win_facts C a CK Hw) as (_ & T & _). rewrite PIH in X. lia.
  - intros a Hc. destruct (pin_clr_img (u a) Hc) as (Hi & Hlg & Hag & He & Hh). rewrite Fimg; [exact (Hclr a Hc) | exact Hi | exact Hag | exact He | exact Hh].
  - rewrite <- Hhdl. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|].
    intros x Hx. cbn in Hx. destruct (proj2 (proj2 pin_hcell) (u x) ltac:(lia)) as (_ & _ & Hag & He).
    assert (Hgx : ~ heap_gap C x) by (apply img_not_gap; unfold inZ; lia).
    assert (Hngx : ~ al_globals x) by (intros G; apply pin_glob in G; exact (Hag G)).
    apply Hfr; [exact (Hno x Hgx Hngx) | exact (Hno' x Hgx Hngx) | intros G; apply pin_errno in G; exact (He G) | lia].
  - exact (FRM_trans C (c_top C) (c_m0 C) m m' Hfrm (FRM_mono C s (c_top C) m m' F Hhi)).
  - exact Hkeep'.
  - intros q k i L Hi. rewrite (Hlive q k i L Hi). exact (Hlive0 q k i L Hi).
  - intros a Ha. destruct (Hdef0 a Ha) as [X|[X|X]]; [left; exact X | right; left; exact X |].
    destruct (Hdef a X) as [Y|[Y|Y]]; [left; exact Y | | right; right; exact Y].
    destruct (ai_owned_where A m (m_vmmaps md) a Hinv Y) as [G|[[G1 G2] _]].
    + left. apply pin_glob in G. rewrite PIH. pose proof pin_ag_img. unfold inZ in *. lia.
    + right; left. split; [exact G1|]. rewrite <- V2. exact G2.
Qed.

(* [comment removed for export] *)
Lemma keep_same : forall C A A', (forall q k, live (c_A0 C) q = Some k -> live A q = Some k) ->
  (forall q, live A' q = live A q) -> forall q k, live (c_A0 C) q = Some k -> live A' q = Some k.
Proof. intros C A A' HK EQ q k L. rewrite EQ. exact (HK q k L). Qed.

Lemma keep_new : forall C A A' (res : word) n, (forall q k, live (c_A0 C) q = Some k -> live A q = Some k) ->
  live A res = None -> live A' res = Some n -> (forall q, q <> res -> live A' q = live A q) ->
  (forall q k, live (c_A0 C) q = Some k -> live A' q = Some k) /\ live (c_A0 C) res = None.
Proof.
  intros C A A' res n HK L0 L1 EQ. split.
  - intros q k L. destruct (bv_eq_dec _ q res) as [E|NE]; [subst q; pose proof (HK res k L); congruence|].
    rewrite (EQ q NE). exact (HK q k L).
  - destruct (live (c_A0 C) res) as [k|] eqn:E; [|reflexivity]. pose proof (HK res k E). congruence.
Qed.

Lemma keep_free : forall C A A' (p : word) n, (forall q k, live (c_A0 C) q = Some k -> live A q = Some k) ->
  live A p = Some n -> live (c_A0 C) p = None -> live A' p = None -> (forall q, q <> p -> live A' q = live A q) ->
  forall q k, live (c_A0 C) q = Some k -> live A' q = Some k.
Proof.
  intros C A A' p n HK L L0 L1 EQ q k Lq. destruct (bv_eq_dec _ q p) as [E|NE]; [subst q; congruence|].
  rewrite (EQ q NE). exact (HK q k Lq).
Qed.

Lemma W_calloc : forall C A m md regs (cnt sz : Z) (ret : word) (s : Z) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 10 = Z_to_bv 64 cnt -> getr regs 11 = Z_to_bv 64 sz ->
  0 <= cnt < 2 ^ 64 -> 0 <= sz < 2 ^ 64 -> 0 <= cnt * sz < 2 ^ 61 ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = al_gp ->
  getr regs 2 = Z_to_bv 64 s -> s mod 16 = 0 -> c_top C - LSTK + CALLOC_STACK <= s -> s <= c_top C ->
  (forall A' m' vm' regs' (res : word),
      W C A' m' (with_vmmaps vm' md) ->
      getr regs' 10 = res -> (forall r, callee_saved r -> getr regs' r = getr regs r) ->
      ( (res = Z_to_bv 64 0 /\ (forall q, live A' q = live A q))
        \/ (u res <> 0 /\ live A res = None /\ live A' res = Some (cnt * sz) /\ live (c_A0 C) res = None /\
            (forall q, q <> res -> live A' q = live A q) /\
            (forall i, 0 <= i < cnt * sz -> m' (at_ res i) = Some (Z_to_bv 8 0)) /\
            u res mod 16 = 0 /\ u res + round16 (cnt * sz) <= alloc_top (c_vm C)) ) ->
      POSTM C A s m m' ->
      realizes al_segs (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes al_segs (mkCfg (mkst regs al_calloc_pc m al_rom) md) S.
Proof.
  intros C A m md regs cnt sz ret s S CK HW H10 H11 Hcnt Hsz Hprod H1 Hret H4 H2 Hs16 Hlo Hhi HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. destruct (w_vm _ _ _ _ HW) as (V1 & V2 & V3 & V4).
  unfold CALLOC_STACK, ALLOC_STACK in *.
  assert (Hs : 0 <= s < 2 ^ 64) by lia.
  eapply (ai_calloc fx A m md regs cnt sz ret (c_sp0 C) (c_argv C) (c_envp C) S
            (w_inv _ _ _ _ HW) (w_pure _ _ _ _ HW) (w_env _ _ _ _ HW) H10 H11 Hcnt Hsz Hprod H1 (pin_ret _ Hret) H4).
  - rewrite H2, u_Z2bv by lia. exact Hs16.
  - rewrite H2, u_Z2bv by lia. rewrite V2. lia.
  - rewrite H2, u_Z2bv by lia. lia.
  - rewrite H2. intros a Ha. rewrite u_Z2bv in Ha by lia. exact (W_call_win C A m md s (1024 + 32) CK HW ltac:(lia) Hhi a Ha).
  - intros A' m' vm' regs' res Hinv' Hres Hcs Hout Hfr Hlive Hdef E1 E2 E3 E4.
    rewrite H2, u_Z2bv in Hfr by lia.
    assert (Hkeep' : (forall q k, live (c_A0 C) q = Some k -> live A' q = Some k) /\
                     (u res <> 0 -> live (c_A0 C) res = None)).
    { destruct Hout as [[-> EQ]|(R1 & R2 & R3 & R4 & R5 & R6)].
      - split; [exact (keep_same C A A' (w_keep _ _ _ _ HW) EQ) | intros X; exfalso; apply X; reflexivity].
      - destruct (keep_new C A A' res _ (w_keep _ _ _ _ HW) R2 R3 R4) as [X Y]. split; [exact X | intros _; exact Y]. }
    destruct Hkeep' as [Hkeep' Hres0].
    destruct (W_after_call C A m md A' m' vm' s (1024 + 32) CK HW ltac:(lia) ltac:(lia) Hhi
                Hinv' Hkeep' Hfr (fun q k i L Hi => Hlive q k i (w_keep _ _ _ _ HW q k L) Hi) Hdef E1 E2 E3 E4) as [HW' F].
    apply (HK A' m' vm' regs' res HW' Hres Hcs); [|split; [exact F|exact Hlive]].
    destruct Hout as [L|(R1 & R2 & R3 & R4 & R5 & R6)]; [left; exact L|right].
    destruct (ai_live_hull A' m' vm' res (cnt * sz) Hinv' R3) as (_ & AL16 & TOP & _).
    rewrite E2, V2 in TOP.
    repeat split; try assumption. exact (Hres0 R1).
Qed.

Lemma W_malloc : forall C A m md regs (n : Z) (ret : word) (s : Z) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 10 = Z_to_bv 64 n -> 0 <= n < 2 ^ 61 ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = al_gp ->
  getr regs 2 = Z_to_bv 64 s -> s mod 16 = 0 -> c_top C - LSTK + ALLOC_STACK <= s -> s <= c_top C ->
  (forall A' m' vm' regs' (res : word),
      W C A' m' (with_vmmaps vm' md) ->
      getr regs' 10 = res -> (forall r, callee_saved r -> getr regs' r = getr regs r) ->
      ( (res = Z_to_bv 64 0 /\ (forall q, live A' q = live A q))
        \/ (u res <> 0 /\ live A res = None /\ live A' res = Some n /\ live (c_A0 C) res = None /\
            (forall q, q <> res -> live A' q = live A q) /\
            u res mod 16 = 0 /\ u res + round16 n <= alloc_top (c_vm C)) ) ->
      POSTM C A s m m' ->
      realizes al_segs (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes al_segs (mkCfg (mkst regs al_malloc_pc m al_rom) md) S.
Proof.
  intros C A m md regs n ret s S CK HW H10 Hn H1 Hret H4 H2 Hs16 Hlo Hhi HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. destruct (w_vm _ _ _ _ HW) as (V1 & V2 & V3 & V4).
  unfold CALLOC_STACK, ALLOC_STACK in *.
  assert (Hs : 0 <= s < 2 ^ 64) by lia.
  eapply (ai_malloc fx A m md regs n ret (c_sp0 C) (c_argv C) (c_envp C) S
            (w_inv _ _ _ _ HW) (w_pure _ _ _ _ HW) (w_env _ _ _ _ HW) H10 Hn H1 (pin_ret _ Hret) H4).
  - rewrite H2, u_Z2bv by lia. exact Hs16.
  - rewrite H2, u_Z2bv by lia. rewrite V2. lia.
  - rewrite H2, u_Z2bv by lia. lia.
  - rewrite H2. intros a Ha. rewrite u_Z2bv in Ha by lia. exact (W_call_win C A m md s 1024 CK HW ltac:(lia) Hhi a Ha).
  - intros A' m' vm' regs' res Hinv' Hres Hcs Hout Hfr Hlive Hdef E1 E2 E3 E4.
    rewrite H2, u_Z2bv in Hfr by lia.
    assert (Hkeep' : (forall q k, live (c_A0 C) q = Some k -> live A' q = Some k) /\
                     (u res <> 0 -> live (c_A0 C) res = None)).
    { destruct Hout as [[-> EQ]|(R1 & R2 & R3 & R4 & R5)].
      - split; [exact (keep_same C A A' (w_keep _ _ _ _ HW) EQ) | intros X; exfalso; apply X; reflexivity].
      - destruct (keep_new C A A' res _ (w_keep _ _ _ _ HW) R2 R3 R4) as [X Y]. split; [exact X | intros _; exact Y]. }
    destruct Hkeep' as [Hkeep' Hres0].
    destruct (W_after_call C A m md A' m' vm' s 1024 CK HW ltac:(lia) ltac:(lia) Hhi
                Hinv' Hkeep' Hfr (fun q k i L Hi => Hlive q k i (w_keep _ _ _ _ HW q k L) Hi) Hdef E1 E2 E3 E4) as [HW' F].
    apply (HK A' m' vm' regs' res HW' Hres Hcs); [|split; [exact F|exact Hlive]].
    destruct Hout as [L|(R1 & R2 & R3 & R4 & R5)]; [left; exact L|right].
    destruct (ai_live_hull A' m' vm' res n Hinv' R3) as (_ & AL16 & TOP & _).
    rewrite E2, V2 in TOP.
    repeat split; try assumption. exact (Hres0 R1).
Qed.

Lemma W_free : forall C A m md regs (p ret : word) (n s : Z) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 10 = p -> live A p = Some n -> live (c_A0 C) p = None ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = al_gp ->
  getr regs 2 = Z_to_bv 64 s -> s mod 16 = 0 -> c_top C - LSTK + ALLOC_STACK <= s -> s <= c_top C ->
  (forall A' m' vm' regs',
      W C A' m' (with_vmmaps vm' md) ->
      (forall r, callee_saved r -> getr regs' r = getr regs r) ->
      live A' p = None -> (forall q, q <> p -> live A' q = live A q) ->
      POSTM C A' s m m' ->
      realizes al_segs (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes al_segs (mkCfg (mkst regs al_free_pc m al_rom) md) S.
Proof.
  intros C A m md regs p ret n s S CK HW H10 Lp Lp0 H1 Hret H4 H2 Hs16 Hlo Hhi HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. destruct (w_vm _ _ _ _ HW) as (V1 & V2 & V3 & V4).
  unfold CALLOC_STACK, ALLOC_STACK in *.
  assert (Hs : 0 <= s < 2 ^ 64) by lia.
  eapply (ai_free fx A m md regs p ret (c_sp0 C) (c_argv C) (c_envp C) S
            (w_inv _ _ _ _ HW) (w_pure _ _ _ _ HW) (w_env _ _ _ _ HW) H10 (or_intror (ex_intro _ n Lp)) H1 (pin_ret _ Hret) H4).
  - rewrite H2, u_Z2bv by lia. exact Hs16.
  - rewrite H2, u_Z2bv by lia. rewrite V2. lia.
  - rewrite H2, u_Z2bv by lia. lia.
  - rewrite H2. intros a Ha. rewrite u_Z2bv in Ha by lia. exact (W_call_win C A m md s 1024 CK HW ltac:(lia) Hhi a Ha).
  - intros A' m' vm' regs' Hinv' Hcs Lp' EQ Hfr Hlive Hdef E1 E2 E3 E4 _.
    rewrite H2, u_Z2bv in Hfr by lia.
    pose proof (keep_free C A A' p n (w_keep _ _ _ _ HW) Lp Lp0 Lp' EQ) as Hkeep'.
    assert (Hdef' : forall a, m a <> None -> u a < al_image_hi \/ owned A a \/ m' a <> None).
    { intros a Ha. destruct (Hdef a Ha) as [X|X]; [right; left; exact X | right; right; exact X]. }
    destruct (W_after_call C A m md A' m' vm' s 1024 CK HW ltac:(lia) ltac:(lia) Hhi Hinv' Hkeep' Hfr
                (fun q k i L Hi => Hlive q k i (Hkeep' q k L) Hi) Hdef' E1 E2 E3 E4) as [HW' F].
    exact (HK A' m' vm' regs' HW' Hcs Lp' EQ (conj F Hlive)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma W_rdn_clr : forall C A m md (a : Z) (n : nat), W C A m md ->
  (forall z, a <= z < a + Z.of_nat n -> inZs ll_clr z) -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  rdn al_segs m (Z_to_bv 64 a) n = rdn al_segs (fun _ => None) (Z_to_bv 64 a) n.
Proof.
  intros C A m md a n HW Hc Ha Hn. apply rdn_ext; rewrite u_Z2bv by lia; [lia|].
  intros x Hx. apply (w_clr _ _ _ _ HW). apply Hc. lia.
Qed.

Lemma W_rdn_ro : forall C A m md (a : Z) (n : nat), W C A m md ->
  fst ll_ro <= a -> a + Z.of_nat n <= snd ll_ro ->
  rdn al_segs m (Z_to_bv 64 a) n = rdn al_segs (fun _ => None) (Z_to_bv 64 a) n.
Proof.
  intros C A m md a n HW Ha Hn. laypins. destruct n as [|n']; [reflexivity|].
  apply rdn_ext; rewrite u_Z2bv by lia; [lia|].
  intros x Hx. apply (W_ro C A m md x HW). unfold inZ. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cs_kept (regs regs' : bvmap 5 word) : Prop := forall r, callee_saved r -> getr regs' r = getr regs r.

Lemma cs_kept_refl : forall R, cs_kept R R.
Proof. intros R r _. reflexivity. Qed.

Lemma cs_kept_trans : forall R1 R2 R3, cs_kept R1 R2 -> cs_kept R2 R3 -> cs_kept R1 R3.
Proof. intros R1 R2 R3 A B r Hr. rewrite (B r Hr). apply A, Hr. Qed.

Lemma cs_cases : forall r : bv 5, callee_saved r ->
  r = 2%bv \/ r = 3%bv \/ r = 4%bv \/ r = 8%bv \/ r = 9%bv \/ r = 18%bv \/ r = 19%bv \/ r = 20%bv \/ r = 21%bv \/ r = 22%bv \/
  r = 23%bv \/ r = 24%bv \/ r = 25%bv \/ r = 26%bv \/ r = 27%bv.
Proof.
  intros r Hr. unfold callee_saved in Hr.
  destruct Hr as [E|[E|[E|[E|[E|Hr]]]]]; [tauto|tauto|tauto|tauto|tauto|].
  pose proof (bv_unsigned_in_range _ r) as RR.
  assert (E : r = Z_to_bv 5 (bv_unsigned r)) by (apply bv_eq; rewrite Z_to_bv_unsigned; symmetry; apply bv_wrap_small; exact RR).
  assert (C : bv_unsigned r = 18 \/ bv_unsigned r = 19 \/ bv_unsigned r = 20 \/ bv_unsigned r = 21 \/ bv_unsigned r = 22 \/
              bv_unsigned r = 23 \/ bv_unsigned r = 24 \/ bv_unsigned r = 25 \/ bv_unsigned r = 26 \/ bv_unsigned r = 27) by lia.
  rewrite E. destruct C as [C|[C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]]; rewrite C;
    repeat (first [left; apply bv_eq; reflexivity | right]); apply bv_eq; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cs_kept_intro : forall R R',
  getr R' 2%bv = getr R 2%bv -> getr R' 3%bv = getr R 3%bv -> getr R' 4%bv = getr R 4%bv -> getr R' 8%bv = getr R 8%bv ->
  getr R' 9%bv = getr R 9%bv -> getr R' 18%bv = getr R 18%bv -> getr R' 19%bv = getr R 19%bv -> getr R' 20%bv = getr R 20%bv ->
  getr R' 21%bv = getr R 21%bv -> getr R' 22%bv = getr R 22%bv -> getr R' 23%bv = getr R 23%bv -> getr R' 24%bv = getr R 24%bv ->
  getr R' 25%bv = getr R 25%bv -> getr R' 26%bv = getr R 26%bv -> getr R' 27%bv = getr R 27%bv -> cs_kept R R'.
Proof.
  intros R R' E2 E3 E4 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 r Hr.
  destruct (cs_cases r Hr) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]]; assumption.
Qed.

(* [comment removed for export] *)
Definition cs_rest : list (bv 5) := [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Lemma cs_kept_of_rest : forall R R', getr R' 2%bv = getr R 2%bv -> getr R' 8%bv = getr R 8%bv -> getr R' 9%bv = getr R 9%bv ->
  (forall r, In r cs_rest -> getr R' r = getr R r) -> cs_kept R R'.
Proof.
  intros R R' E2 E8 E9 ER. apply cs_kept_intro; try assumption; apply ER; cbn [In cs_rest];
  repeat (first [left; reflexivity | right]).
Qed.

Lemma cs_rest_of_kept : forall R R', cs_kept R R' -> forall r, In r cs_rest -> getr R' r = getr R r.
Proof.
  intros R R' K r Hr. apply K. cbn [In cs_rest] in Hr. unfold callee_saved.
  repeat (destruct Hr as [<-|Hr]; [first [ do 1 right; left; reflexivity | do 2 right; left; reflexivity
                                          | do 5 right; vm_compute; split; discriminate ] |]).
  destruct Hr.
Qed.

Lemma cs_kept_get : forall R R' (r : bv 5), cs_kept R R' -> callee_saved r -> getr R' r = getr R r.
Proof. intros R R' r K Hr. exact (K r Hr). Qed.

Lemma cs2 : callee_saved 2%bv. Proof. unfold callee_saved; tauto. Qed.
Lemma cs3 : callee_saved 3%bv. Proof. unfold callee_saved; tauto. Qed.
Lemma cs4 : callee_saved 4%bv. Proof. unfold callee_saved; tauto. Qed.
Lemma cs8 : callee_saved 8%bv. Proof. unfold callee_saved; tauto. Qed.
Lemma cs9 : callee_saved 9%bv. Proof. unfold callee_saved; tauto. Qed.
Lemma cs18 : callee_saved 18%bv. Proof. unfold callee_saved; do 5 right; vm_compute; split; discriminate. Qed.
Lemma cs19 : callee_saved 19%bv. Proof. unfold callee_saved; do 5 right; vm_compute; split; discriminate. Qed.
Lemma cs20 : callee_saved 20%bv. Proof. unfold callee_saved; do 5 right; vm_compute; split; discriminate. Qed.
Lemma cs21 : callee_saved 21%bv. Proof. unfold callee_saved; do 5 right; vm_compute; split; discriminate. Qed.
Lemma cs22 : callee_saved 22%bv. Proof. unfold callee_saved; do 5 right; vm_compute; split; discriminate. Qed.
Lemma cs23 : callee_saved 23%bv. Proof. unfold callee_saved; do 5 right; vm_compute; split; discriminate. Qed.
Lemma cs24 : callee_saved 24%bv. Proof. unfold callee_saved; do 5 right; vm_compute; split; discriminate. Qed.
Lemma cs25 : callee_saved 25%bv. Proof. unfold callee_saved; do 5 right; vm_compute; split; discriminate. Qed.
Lemma cs26 : callee_saved 26%bv. Proof. unfold callee_saved; do 5 right; vm_compute; split; discriminate. Qed.
Lemma cs27 : callee_saved 27%bv. Proof. unfold callee_saved; do 5 right; vm_compute; split; discriminate. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma W_entry : forall C md m1, Cok C -> c_vm C = m_vmmaps md ->
  ainv (c_A0 C) (c_m0 C) (m_vmmaps md) -> md_pure md -> al_env (c_sp0 C) (c_argv C) (c_envp C) (c_m0 C) ->
  (forall a, win C a -> c_m0 C a <> None /\ ~ owned (c_A0 C) a) ->
  (forall a, inZs ll_clr (u a) -> c_m0 C a = None) ->
  (forall a, m1 a <> c_m0 C a -> win C a \/ hcell a) ->
  (forall a, c_m0 C a <> None -> m1 a <> None) ->
  rdn al_segs m1 (Z_to_bv 64 ll_hcell) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 ll_devnull)) ->
  W C (c_A0 C) m1 md.
Proof.
  intros C md m1 CK Evm Hinv Hpure Henv Hwin Hclr Hch Hgr Hhdl.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. set (m := c_m0 C) in *. set (A := c_A0 C) in *.
  assert (Hhc_no : forall a, hcell a -> ~ owned A a).
  { intros a Hh Ho. unfold hcell in Hh. destruct (ai_owned_where A m (m_vmmaps md) a Hinv Ho) as [G|[[G _] _]].
    - apply pin_glob in G. destruct (proj2 (proj2 pin_hcell) (u a) Hh) as (_ & _ & X & _). exact (X G).
    - destruct (pin_grant a G) as [X _]. apply X. unfold inZ. lia. }
  assert (Hhc_img : forall a, hcell a -> inZ ll_img (u a)) by (intros a Hh; unfold hcell, inZ in *; lia).
  assert (Heq : forall a, ~ win C a -> ~ hcell a -> m1 a = m a).
  { intros a H1 H2. destruct (omem_eq_dec (m1 a) (m a)) as [E|NE]; [exact E|]. exfalso. destruct (Hch a NE) as [X|X]; [exact (H1 X) | exact (H2 X)]. }
  assert (Himg_nw : forall a, inZ ll_img (u a) -> ~ win C a).
  { intros a Hi Hw. destruct (win_facts C a CK Hw) as (X & _). exact (X Hi). }
  assert (Htop_nw : forall a, c_top C <= u a -> ~ win C a) by (intros a Ha Hw; unfold win in Hw; lia).
  assert (Htop_nh : forall a, c_top C <= u a -> ~ hcell a) by (intros a Ha Hh; unfold hcell in Hh; lia).
  split.
  - apply (ai_frame A m m1 (m_vmmaps md) Hinv).
    + intros a Ho _. apply Heq; [intros Hw; exact (proj2 (Hwin a Hw) Ho) | intros Hh; exact (Hhc_no a Hh Ho)].
    + intros a _ Hx. exact (Hgr a Hx).
    + intros a [G1 G2] Hx. destruct (omem_eq_dec (m1 a) (m a)) as [E|NE]; [rewrite <- E; exact Hx|].
      destruct (Hch a NE) as [X|X]; [exact (proj1 (Hwin a X))|]. exfalso. destruct (pin_grant a G1) as [Y _]. exact (Y (Hhc_img a X)).
  - exact Hpure.
  - apply (pin_env_frame _ _ _ m m1 Henv). intros a [Ha|[Ha|[[Ha _]|Ha]]].
    + apply Heq; [apply Himg_nw; unfold inZ in *; lia | unfold hcell; intros X; destruct (proj2 (proj2 pin_hcell) (u a) X) as (Y & _); exact (Y Ha)].
    + destruct (pin_clr_img (u a) Ha) as (Hi & _ & _ & _ & Hh). apply Heq; [apply Himg_nw; exact Hi | exact Hh].
    + apply Heq; [apply Himg_nw; unfold inZ in *; lia | unfold hcell; intros X; destruct (proj2 (proj2 pin_hcell) (u a) X) as (_ & Y & _); exact (Y Ha)].
    + apply Heq; [apply Htop_nw | apply Htop_nh]; destruct CK; lia.
  - rewrite <- Evm. repeat split; reflexivity.
  - intros a Hw. apply Hgr. exact (proj1 (Hwin a Hw)).
  - intros a Hc. destruct (pin_clr_img (u a) Hc) as (Hi & _ & _ & _ & Hh). rewrite Heq; [exact (Hclr a Hc) | apply Himg_nw; exact Hi | exact Hh].
  - exact Hhdl.
  - intros a H1 H2 H3 H4 H5. apply Heq; [| exact H4]. intros Hw. apply H5. unfold win, scratch in *. lia.
  - intros q k L. exact L.
  - intros q k i L Hi. pose proof (ai_live_hull A m (m_vmmaps md) q k Hinv L) as (Hk0 & _ & TOP & OWN).
    pose proof (round16_ge k Hk0). destruct (OWN i ltac:(lia)) as (Ho & _). apply Heq.
    + intros Hw. exact (proj2 (Hwin _ Hw) Ho).
    + intros Hh. exact (Hhc_no _ Hh Ho).
  - intros a Hx. right; right. exact (Hgr a Hx).
Qed.

End Defs.

(* [comment removed for export] *)
Ltac laypins :=
  let P1 := fresh "PIN" in let P2 := fresh "PIN" in let P3 := fresh "PIN" in let P4 := fresh "PIN" in
  let P5 := fresh "PIN" in let P6 := fresh "PIN" in let P7 := fresh "PIN" in let P8 := fresh "PIN" in let P9 := fresh "PIN" in
  let P10 := fresh "PIN" in
  pose proof pin_img64 as P1; pose proof pin_ro_img as P2; pose proof pin_lg_img as P3; pose proof pin_ag_img as P4;
  pose proof pin_errno_img as P5; pose proof (proj1 pin_hcell) as P6; pose proof (proj1 (proj2 pin_hcell)) as P7;
  pose proof pin_devnull as P8; pose proof LSTK_val as P9; pose proof pin_ro_below as P10.

(* [comment removed for export] *)
Ltac wp_win CK :=
  first [ apply (WP_win _ _ _ _ _ _ _ _ _ CK);
          [ wp_win CK
          | first [apply sub_live_refl | assumption | eapply W_sub0; eassumption]
          | rewrite ?u_Z2bv by lia; lia
          | rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
          | lia ]
        | split; [assumption | first [apply POSTM_refl | assumption]] ].

(* [comment removed for export] *)
Ltac cs_of r :=
  lazymatch r with
  | 2%bv => constr:(cs2) | 3%bv => constr:(cs3) | 4%bv => constr:(cs4) | 8%bv => constr:(cs8) | 9%bv => constr:(cs9)
  | 18%bv => constr:(cs18) | 19%bv => constr:(cs19) | 20%bv => constr:(cs20) | 21%bv => constr:(cs21) | 22%bv => constr:(cs22)
  | 23%bv => constr:(cs23) | 24%bv => constr:(cs24) | 25%bv => constr:(cs25) | 26%bv => constr:(cs26) | 27%bv => constr:(cs27)
  end.
Ltac notin_lit :=
  cbn [In]; let HH := fresh in intros HH;
  repeat (destruct HH as [HH|HH]; [apply bv_eq in HH; cbv in HH; discriminate HH|]); exact HH.
Ltac in_lit := try unfold cs_rest; cbn [In]; repeat (first [ left; reflexivity | right ]).
Ltac csr1 :=
  match goal with
  | |- context [getr ?R' ?r] =>
      first [ match goal with E : getr R' r = _ |- _ => rewrite E end
            | match goal with K : cs_kept ?R R' |- _ => let c := cs_of r in rewrite (cs_kept_get R R' r K c) end
            | match goal with RR : forall x, In x _ -> getr R' x = _ |- _ => rewrite (RR r) by in_lit end
            | match goal with AG : regs_agree ?P ?R R' |- _ => rewrite (AG r) by notin_lit end ]
  end.
Ltac csr := repeat csr1.
(* [comment removed for export] *)
Ltac rest_solve :=
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [In cs_rest] in Hx; repeat (destruct Hx as [<-|Hx]; [csr; reflexivity|]); destruct Hx.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
