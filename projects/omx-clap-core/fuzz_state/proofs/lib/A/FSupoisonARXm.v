(* The AR -> ARU transfer of a Theorem Labs lane's FROZEN allocator interface (a Theorem Labs lane; brief L16-AruIfaceM).

   a Theorem Labs lane's frame-generic Allocate / Deallocate walks (a working branch 95e6f1d72b6, frozen) take the
   allocator invariant as a parameter [ARX : Z -> alayout -> astate -> world segs -> (word -> option byte) -> Model ->
   Prop] and read it only through interface RECORDS (lib/Reusable/AGif0n.v AIface / AIfaceK / AIfaceM, AGif4.v AIfaceS,
   DGif0.v DIface, DIfaceR.v DIfaceR).  cgif instantiates ARX with [inst = I /\ AR] ([ARX_AR] below); fuzz_state
   instantiates it with the any-user-poison invariant [inst = I /\ FSupoison.ARU .. Up ..] ([ARX_ARU]: the poison set
   Up fixed outside the call, unchanged across it).  The transfers prove, per record, "the AR instance satisfies it =>
   the ARU instance satisfies it", with ARX abstract, so fs gets the ARU form by instantiation, with no second walk.
   They are in three files, one per record family, over this file: lib/A/FSupoisonARXmA.v (AGif0n: aiface_U,
   aifaceK_U, ifaceM_U), lib/A/FSupoisonARXmS.v (AGif4: ifaceS_U), lib/A/FSupoisonARXmD.v (DGif0: diface_U).  A field
   that IS a callee contract (AIfaceM.if_refill; DIface's di_enqueue / di_drain / di_rchunk / di_cdealloc; every
   DIfaceR field) is not transferred: it runs on the poisoned memory, so the ARU record takes its ARU form as a premise,
   which fs builds from its ARU twins of the released callee specs (a Theorem Labs lane decision, 12:13Z).

   This file is the transfers' shared kit.  It names no address of cgif's or of fs's: it Requires only lib/Reusable
   files and FSupoison.  The image's geometry enters the transfers only through the image classes (ImgBase.AImg,
   ImgBaseAG.AGImg, ImgBaseAGS.AImgS, ImgBaseDG.DImg) and through named premises, each discharged per image
   (lib/A|B/FSupoisonARX.v section 3 for [inst_low] / [zones_free]).

   1. Sections 0 and 1 (moved here from lib/A/FSupoisonARX.v, same names, a Theorem Labs lane 12:3xZ): list / arithmetic helpers,
      and where a user-poisoned shadow byte can be ([ush_lo]: in [shadow (image end), kHighMemBeg), so every
      application address and every image-shadow address is off Up), with the memory transfer across
      [FSupoison.unpoison] at an address off Up ([val_mem_unpoison], [cell_holds_unpoison], [apresent_unpoison_*],
      [aview_unpoison_off]) and the off-Up facts for the allocator's own cells ([owned_core_off_ush],
      [const_cell_off_ush], [thread_off_ush], [high_off_ush], [low_off_ush], [val250_off_ush]).
   2. The two instances and the image premises: [ARX_AR] / [ARX_ARU]; [inst_low] (the instance object lies below the
      shadow) and [zones_free] (a zone a callee is entered with holds no shadow byte of a live block).
   3. The kit: raw / aview equalities and visibility move across the unpoisoning at every address ([unpoison_eq],
      [aview_unpoison_eq], [aview_unpoison_some]); the band of an Up byte ([ush_band]); owned extents, secondary maps
      and the stack are off Up; [ARU_rebuild] / [ARU_rebuild_raw] (ARU at a post state from AR there over the
      unpoisoned memory, the blocks that hold Up's ranges still live, Up's bytes unchanged); [fpreU] (Deallocate's
      range premise, = lib/A/FSRealloc_inst.FS_fpre); [img_low] (the image's OOM byte and errno below the shadow).

   No Axiom, no Admitted. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0q YG0s YG0t.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.
Fail Definition probe_SH : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI14.sink_syms := _.

Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 0. List / arithmetic helpers.                                                                                     *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Lemma pairwise_app_rel {X} (R : X -> X -> Prop) : forall l1 l2 x y,
pairwise R (l1 ++ l2) -> In x l1 -> In y l2 -> R x y.
Proof.
intros l1. induction l1 as [|z t IH]; intros l2 x y P Hx Hy; [destruct Hx|].
cbn [app pairwise] in P. destruct P as [F P]. destruct Hx as [<-|Hx].
- exact (proj1 (Forall_forall _ _) F y (in_or_app t l2 y (or_intror Hy))).
- exact (IH l2 x y P Hx Hy).
Qed.

Lemma nodup_app_notin {X} : forall (l1 l2 : list X) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
intros l1. induction l1 as [|z t IH]; intros l2 x N H1 H2; [destruct H1|].
cbn [app] in N. apply List.NoDup_cons_iff in N as [Nz N].
destruct H1 as [<-|H1]; [apply Nz, in_or_app; right; exact H2 | exact (IH l2 x N H1 H2)].
Qed.

Lemma shadow_addr_mono : forall a b, a <= b -> shadow_addr a <= shadow_addr b.
Proof. intros a b H. unfold shadow_addr. pose proof (Z.div_le_mono a b 8 ltac:(lia) H). lia. Qed.

Lemma wz64 : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a.
Proof.
intros a Ha. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply Z.mod_small. exact Ha.
Qed.

Lemma bvz64 : forall a, bv_unsigned (Z_to_bv 64 a) = a mod 2 ^ 64.
Proof. intros a. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma bv_range64 : forall x : word, 0 <= bv_unsigned x < 2 ^ 64.
Proof.
intros x. pose proof (bv_unsigned_in_range 64 x) as H. change (bv_modulus 64) with (2 ^ 64) in H. exact H.
Qed.

(* [from_primary] on the hit path's size window. *)
Lemma from_primary_64512 : forall n, 0 <= n <= 64512 -> from_primary n = true.
Proof.
intros n Hn. unfold from_primary. apply Z.leb_le.
unfold needed_primary, rounded_size, round_up, rz_size, rz_log, kMaxSize.
assert (DIV : forall hi, 8 <= hi -> n <= hi -> (Z.max n 8 + 8 - 1) / 8 <= (hi + 7) / 8).
{ intros hi H8 Hhi. exact (Z.div_le_mono (Z.max n 8 + 8 - 1) (hi + 7) 8 ltac:(lia) ltac:(lia)). }
destruct (Z.leb_spec n 48) as [H0|H0];
[ pose proof (DIV 48 ltac:(lia) ltac:(lia)) as D; assert (E : (48 + 7) / 8 = 6) by reflexivity; rewrite E in D;
  change (Z.shiftl 16 0) with 16; lia |].
destruct (Z.leb_spec n 96) as [H1|H1];
[ pose proof (DIV 96 ltac:(lia) ltac:(lia)) as D; assert (E : (96 + 7) / 8 = 12) by reflexivity; rewrite E in D;
  change (Z.shiftl 16 1) with 32; lia |].
destruct (Z.leb_spec n 448) as [H2|H2];
[ pose proof (DIV 448 ltac:(lia) ltac:(lia)) as D; assert (E : (448 + 7) / 8 = 56) by reflexivity; rewrite E in D;
  change (Z.shiftl 16 2) with 64; lia |].
destruct (Z.leb_spec n 3968) as [H3|H3];
[ pose proof (DIV 3968 ltac:(lia) ltac:(lia)) as D; assert (E : (3968 + 7) / 8 = 496) by reflexivity; rewrite E in D;
  change (Z.shiftl 16 3) with 128; lia |].
destruct (Z.leb_spec n 16128) as [H4|H4];
[ pose proof (DIV 16128 ltac:(lia) ltac:(lia)) as D; assert (E : (16128 + 7) / 8 = 2016) by reflexivity; rewrite E in D;
  change (Z.shiftl 16 4) with 256; lia |].
destruct (Z.leb_spec n 32256) as [H5|H5];
[ pose proof (DIV 32256 ltac:(lia) ltac:(lia)) as D; assert (E : (32256 + 7) / 8 = 4032) by reflexivity; rewrite E in D;
  change (Z.shiftl 16 5) with 512; lia |].
destruct (Z.leb_spec n 64512) as [H6|H6];
[ pose proof (DIV 64512 ltac:(lia) ltac:(lia)) as D; assert (E : (64512 + 7) / 8 = 8064) by reflexivity; rewrite E in D;
  change (Z.shiftl 16 6) with 1024; lia | lia].
Qed.

Lemma rz_log_range : forall n, 0 <= rz_log n <= 7.
Proof.
intros n. unfold rz_log. repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia.
Qed.

Lemma rz_size_eq : forall n, rz_size n = 16 * 2 ^ rz_log n.
Proof.
intros n. unfold rz_size. rewrite Z.shiftl_mul_pow2; [reflexivity|]. pose proof (rz_log_range n). lia.
Qed.

Lemma prim_class_region : forall cl off, 0 <= off < 2 ^ 32 -> prim_class (region_off cl + off) = cl.
Proof.
intros cl off Ho. unfold prim_class, region_off.
rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
rewrite Z.div_add_l by lia. rewrite (Z.div_small off (2 ^ 32) Ho). lia.
Qed.

Lemma upd_chunk_keeps : forall l k0 k, In k0 l -> ck_beg k0 <> ck_beg k -> In k0 (upd_chunk l k).
Proof.
intros l. induction l as [|k1 t IH]; intros k0 k Hin Hne; [destruct Hin|].
cbn [upd_chunk]. destruct (sptr_eqb (ck_beg k1) (ck_beg k)) eqn:E.
- apply sptr_eqb_spec in E. destruct Hin as [<-|Hin]; [exfalso; exact (Hne E) | right; exact Hin].
- destruct Hin as [<-|Hin]; [left; reflexivity | right; exact (IH k0 k Hin Hne)].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. Where a user-poisoned shadow byte can be, and the memory transfer that follows.                               *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Section geo. Context {rc : YM05.RunCeil}.

(* The addresses the unpoisoning does not touch, as a fact of the layout alone: below the shadow of the
   image's end (so below every live block's shadow) or at/above kHighMemBeg (so above all shadow). *)
Definition ush_free (ly : alayout) (a : Z) : Prop :=
a < shadow_addr (fst (ly_img ly) + snd (ly_img ly)) \/ kHighMemBeg <= a.

(* The same, as the memory-level fact the transfer uses. *)
Definition off_ush (Up : list (Z * Z)) (a : Z) : Prop := FSP.in_ush Up (a mod 2 ^ 64) = false.

Lemma off_ush_w : forall Up (x : word), off_ush Up (bv_unsigned x) -> FSP.in_ush Up (bv_unsigned x) = false.
Proof.
intros Up x H. unfold off_ush in H. rewrite (Z.mod_small _ _ (bv_range64 x)) in H. exact H.
Qed.

Lemma img_in_static : forall ly, In (ly_img ly) (static_extents ly).
Proof. intros ly. unfold static_extents. apply in_or_app. right. right. left. reflexivity. Qed.

(* A live block lies above the image: its chunk is primary (in [ly_prim], above kHighMemBeg) or secondary
   (a map disjoint from the image, and too big to fit below it: kPage + kMaxSize < sec_map_size). *)
Lemma block_above_img : forall B ly S rd p n, ARm B ly S rd -> In (p, n) (ablocks B ly S) ->
fst (ly_img ly) + snd (ly_img ly) <= p.
Proof.
intros B ly S rd p n M Hb.
destruct (FSP.ablock_chunk B ly S p n Hb) as (k & Hk & Hu & _).
pose proof (am_layout B ly S rd M) as LO.
pose proof (am_placed B ly S rd M) as [PL PD].
pose proof (lo_img ly LO) as (I0 & I1 & I2 & I3).
pose proof (lo_high ly LO) as [HP1 HP2].
pose proof (lo_space_in ly LO) as [SP1 SP2].
pose proof (chunk_facts B ly S rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
rewrite G4 in Hu.
destruct (ck_beg k) as [|off|r o|c q] eqn:Eb; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & _ & _).
  assert (R0 : 0 <= region_off (prim_class off)).
  { unfold region_off. rewrite Z.shiftl_mul_pow2 by lia.
    pose proof (Z.pow_pos_nonneg 2 32 ltac:(lia) ltac:(lia)). nia. }
  unfold region_base in Gbase. unfold kImgEnd, kImgLo, kHighMemBeg in *. lia.
- destruct GG as (Ho & Hfp & Gbase & Gext & Gin & Gal & _).
  pose proof (proj1 (Forall_forall _ _) PL _ Gin) as (PA & [A1 A2] & A3). cbn [fst snd] in PA, A1, A2, A3.
  pose proof (pairwise_app_rel zdisjoint (sec_extents ly S) (static_extents ly)
     (ly_sec ly r, sec_map_size (ck_req k)) (ly_img ly) PD Gin (img_in_static ly)) as D.
  unfold zdisjoint in D. cbn [fst snd] in D.
  pose proof (secondary_geometry (ck_req k) ltac:(lia) Hfp) as (S1 & S2 & S3 & S4 & S5 & S6).
  unfold kImgLo, kImgEnd, kPage, kMaxSize in *. lia.
Qed.

(* A user-poisoned shadow byte lies in the band the allocator's own cells avoid. *)
Lemma ush_lo : forall segs B ly S Up W mem md s, FSP.ARU segs B ly S Up W mem md -> FSP.in_ush Up s = true ->
shadow_addr (fst (ly_img ly) + snd (ly_img ly)) <= s < kHighMemBeg.
Proof.
intros segs B ly S Up W mem md s H Hs.
pose proof (FSP.ush_facts segs B ly S Up W mem md s H Hs) as (_ & _ & HI).
destruct (FSP.ush_granule B ly S Up s (FSP.ARU_ok segs B ly S Up W mem md H) Hs)
  as (g & p & n & Hbl & G8 & Gs & Gp & Gn).
pose proof (block_above_img B ly S _ p n (FSP.ARU_ARm segs B ly S Up W mem md H) Hbl) as AB.
rewrite <- Gs in HI |- *. split; [apply shadow_addr_mono; lia | exact HI].
Qed.

Lemma ush_free_off : forall segs B ly S Up W mem md a, FSP.ARU segs B ly S Up W mem md ->
0 <= a < 2 ^ 64 -> ush_free ly a -> off_ush Up a.
Proof.
intros segs B ly S Up W mem md a H Ha HF. unfold off_ush. rewrite (Z.mod_small a (2 ^ 64) Ha).
destruct (FSP.in_ush Up a) eqn:E; [|reflexivity]. exfalso.
pose proof (ush_lo segs B ly S Up W mem md a H E) as [L1 L2]. unfold ush_free in HF. lia.
Qed.

(* ---- memory transfer at an address the unpoisoning does not touch ---- *)

Lemma unpoison_off : forall Up m a, off_ush Up a -> FSP.unpoison Up m (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof. intros Up m a H. apply FSP.unpoison_out. rewrite bvz64. exact H. Qed.

Lemma mrestrict_unpoison_off : forall (H : word -> bool) Up m a, off_ush Up a ->
mrestrict H (FSP.unpoison Up m) (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a).
Proof. intros Hh Up m a E. unfold mrestrict. rewrite (unpoison_off Up m a E). reflexivity. Qed.

Lemma mbyte_unpoison_off : forall segs (H : word -> bool) Up m a, off_ush Up a ->
mbyte segs (mrestrict H (FSP.unpoison Up m)) a = mbyte segs (mrestrict H m) a.
Proof. intros segs Hh Up m a E. unfold mbyte. rewrite (mrestrict_unpoison_off Hh Up m a E). reflexivity. Qed.

Lemma val_mem_unpoison : forall segs (H : word -> bool) Up m a (w : nat) val,
(forall k, 0 <= k < Z.of_nat w -> off_ush Up (a + k)) ->
(val_mem segs (mrestrict H (FSP.unpoison Up m)) a w val <-> val_mem segs (mrestrict H m) a w val).
Proof.
intros segs Hh Up m a w val HO. unfold val_mem. split; intros HV k Hk; specialize (HV k Hk);
rewrite (mbyte_unpoison_off segs Hh Up m (a + Z.of_nat k)) in * by (apply HO; lia); exact HV.
Qed.

Lemma apresent_unpoison_fwd : forall (H : word -> bool) Up m a,
apresent H m a -> apresent H (FSP.unpoison Up m) a.
Proof.
intros Hh Up m a [E1 [b E2]]. split; [exact E1|].
destruct (FSP.in_ush Up (bv_unsigned (Z_to_bv 64 a))) eqn:Ei.
- exists (Z_to_bv 8 0). apply FSP.unpoison_in. exact Ei.
- exists b. rewrite (FSP.unpoison_out Up m _ Ei). exact E2.
Qed.

Lemma apresent_unpoison_bwd : forall (H : word -> bool) Up m a, off_ush Up a ->
apresent H (FSP.unpoison Up m) a -> apresent H m a.
Proof.
intros Hh Up m a E [E1 [b E2]]. split; [exact E1|]. exists b. rewrite <- (unpoison_off Up m a E). exact E2.
Qed.

(* The unpoisoning preserves an implication between presences. *)
Lemma apresent_unpoison_mono : forall (H : word -> bool) Up m1 m2 a,
(apresent H m1 a -> apresent H m2 a) ->
apresent H (FSP.unpoison Up m1) a -> apresent H (FSP.unpoison Up m2) a.
Proof.
intros Hh Up m1 m2 a HI [E1 Hb]. destruct (FSP.in_ush Up (bv_unsigned (Z_to_bv 64 a))) eqn:Ei.
- split; [exact E1|]. exists (Z_to_bv 8 0). apply FSP.unpoison_in. exact Ei.
- apply apresent_unpoison_fwd. apply HI. split; [exact E1|].
  destruct Hb as [b Hb]. exists b. rewrite <- (FSP.unpoison_out Up m1 _ Ei). exact Hb.
Qed.

Lemma aview_unpoison_off : forall segs (H : word -> bool) Up m a, off_ush Up a ->
aview segs H (FSP.unpoison Up m) a = aview segs H m a.
Proof. intros segs Hh Up m a E. apply FSP.aview_unpoison_out. rewrite bvz64. exact E. Qed.

Lemma cell_holds_unpoison : forall segs B ly (H : word -> bool) Up m c,
(forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> off_ush Up (aeval B ly (c_at c) + k)) ->
cell_holds B ly (aview segs H (FSP.unpoison Up m)) c -> cell_holds B ly (aview segs H m) c.
Proof.
intros segs B ly Hh Up m c HO HC. unfold cell_holds in *. destruct (c_val c) as [e|mask val].
- intros k Hk. rewrite <- (aview_unpoison_off segs Hh Up m (aeval B ly (c_at c) + Z.of_nat k))
    by (apply HO; lia).
  exact (HC k Hk).
- destruct HC as (b & Hb & Hm). exists b. split; [|exact Hm].
  rewrite <- (aview_unpoison_off segs Hh Up m (aeval B ly (c_at c)));
  [ exact Hb
  | replace (aeval B ly (c_at c)) with (aeval B ly (c_at c) + 0) by lia; apply HO; lia ].
Qed.

(* A byte that reads 250 through ARU's view is not a user-poisoned byte: a poisoned one reads 0 there. *)
Lemma val250_off_ush : forall segs Up (W : world segs) m s,
w_H W (Z_to_bv 64 s) = false -> val_mem segs (mrestrict (w_H W) (FSP.unpoison Up m)) s 1 250 -> off_ush Up s.
Proof.
intros segs Up W m s EH HV. unfold off_ush.
destruct (FSP.in_ush Up (s mod 2 ^ 64)) eqn:E; [|reflexivity]. exfalso.
assert (EB : FSP.in_ush Up (bv_unsigned (Z_to_bv 64 s)) = true) by (rewrite bvz64; exact E).
specialize (HV 0%nat ltac:(lia)). cbn [Z.of_nat] in HV. rewrite Z.add_0_r in HV.
unfold mbyte, mrestrict in HV. rewrite EH, (FSP.unpoison_in Up m _ EB) in HV.
injection HV as HV. revert HV. vm_compute. discriminate.
Qed.

(* ---- the cells the allocator's own metadata lives in are never user-poisoned ---- *)

Lemma owned_core_off_ush : forall segs B ly S Up W mem md a, FSP.ARU segs B ly S Up W mem md ->
owned_core B ly a -> off_ush Up a.
Proof.
intros segs B ly S Up W mem md a H HO.
pose proof (FSP.ARU_ARm segs B ly S Up W mem md H) as M.
pose proof (am_layout B ly S _ M) as LO.
pose proof (lo_img ly LO) as (I0 & I1 & I2 & I3).
pose proof (lo_app ly LO) as APP.
pose proof (am_static_img B ly S _ M) as SIMG.
pose proof ASAN_CEIL_range as [CR _].
assert (IMG8 : (fst (ly_img ly) + snd (ly_img ly)) mod 8 = 0).
{ unfold page_aligned in I3. apply Z.mod_divide in I3 as [q Hq]; [|lia]. rewrite I0, Hq.
  unfold kImgLo. replace (65536 + q * 4096) with ((8192 + q * 512) * 8) by lia. apply Z.mod_mul. lia. }
assert (POS : 0 <= fst (ly_img ly) + snd (ly_img ly)) by (unfold kImgLo in *; lia).
assert (DIV0 : 0 <= (fst (ly_img ly) + snd (ly_img ly)) / 8)
  by (apply Z.div_pos; lia).
assert (SH8 : forall u w, 0 <= u -> 0 <= w -> u + w <= fst (ly_img ly) + snd (ly_img ly) ->
  shadow_addr u + (w + 7) / 8 <= shadow_addr (fst (ly_img ly) + snd (ly_img ly))).
{ intros u w Hu Hw Huw. unfold shadow_addr.
  assert (D1 : u / 8 + (w + 7) / 8 <= (u + w + 7) / 8).
  { pose proof (Z.div_mod u 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound u 8 ltac:(lia)) as MB.
    assert (E : (u + w + 7) / 8 = u / 8 + (u mod 8 + w + 7) / 8).
    { replace (u + w + 7) with ((u mod 8 + w + 7) + (u / 8) * 8) by lia.
      rewrite Z.div_add by lia. lia. }
    rewrite E. pose proof (Z.div_le_mono (w + 7) (u mod 8 + w + 7) 8 ltac:(lia) ltac:(lia)). lia. }
  assert (D2 : (u + w + 7) / 8 <= (fst (ly_img ly) + snd (ly_img ly) + 7) / 8)
    by (apply Z.div_le_mono; lia).
  assert (D3 : (fst (ly_img ly) + snd (ly_img ly) + 7) / 8 = (fst (ly_img ly) + snd (ly_img ly)) / 8).
  { apply Z.mod_divide in IMG8 as [q Hq]; [|lia]. rewrite Hq.
    replace (q * 8 + 7) with (7 + q * 8) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_mul by lia.
    assert (E7 : 7 / 8 = 0) by reflexivity. rewrite E7. lia. }
  lia. }
assert (STATIC : forall r, In r (as_owned_static B) ->
  fst (ly_img ly) <= fst r /\ fst r + snd r <= fst (ly_img ly) + snd (ly_img ly)).
{ intros r Hr. exact (proj1 (Forall_forall _ _) SIMG r
   (in_or_app (as_owned_static B) (as_zero_shadow B) r (or_introl Hr))). }
assert (STSZ : forall r, In r (as_owned_static B) -> 4096 <= fst r /\ 0 <= snd r).
{ intros r Hr. pose proof (proj1 (Forall_forall _ _) (aso_static B (am_syms B ly S _ M)) r Hr) as (T1 & T2 & _).
  exact (conj T1 T2). }
assert (FREE : 0 <= a < 2 ^ 64 /\ ush_free ly a).
{ destruct HO as [HS | [HC | HS]].
  - apply Exists_exists in HS as (r & Hr & Hin). destruct (STATIC r Hr) as [Q1 Q2]. destruct (STSZ r Hr) as [Q3 Q4].
    unfold in_zr in Hin. cbn [fst snd] in Hin.
    unfold ush_free, shadow_addr, SHADOW_OFF, kImgLo, kImgEnd in *. split; [lia | left; lia].
  - apply Exists_exists in HC as (r & Hr & Hin).
    assert (HrO : In r (owned_extents ly))
      by (unfold core_extents in Hr; unfold owned_extents; cbn [In] in *; tauto).
    pose proof (proj1 (Forall_forall _ _) APP r HrO) as [P1 P2]. unfold in_zr in Hin. cbn [fst snd] in Hin.
    unfold ush_free, shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
    destruct P2 as [P2|[P2 P3]].
    + split; [lia | left; lia].
    + split; [lia | right; lia].
  - apply Exists_exists in HS as (r & Hr & Hin). destruct (STATIC r Hr) as [Q1 Q2]. destruct (STSZ r Hr) as [Q3 Q4].
    unfold in_zr in Hin. cbn [fst snd] in Hin.
    pose proof (SH8 (fst r) (snd r) ltac:(lia) ltac:(lia) ltac:(lia)) as SH.
    assert (DD : (fst (ly_img ly) + snd (ly_img ly)) / 8 <= kImgEnd / 8)
      by (apply Z.div_le_mono; unfold kImgLo, kImgEnd in *; lia).
    assert (EE : kImgEnd / 8 = 847360) by reflexivity.
    pose proof (Z.div_pos (fst r) 8 ltac:(lia) ltac:(lia)).
    unfold ush_free, shadow_addr, SHADOW_OFF, kImgEnd in *.
    split; [lia | left; lia]. }
exact (ush_free_off segs B ly S Up W mem md a H (proj1 FREE) (proj2 FREE)).
Qed.

Lemma const_cell_off_ush : forall segs B ly S Up W mem md c, FSP.ARU segs B ly S Up W mem md ->
In c (as_const B ly) -> forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> off_ush Up (aeval B ly (c_at c) + k).
Proof.
intros segs B ly S Up W mem md c H Hc k Hk.
pose proof (FSP.ARU_ARm segs B ly S Up W mem md H) as M.
pose proof (proj1 (Forall_forall _ _) (am_const_owned B ly S _ M) c Hc) as CO.
exact (owned_core_off_ush segs B ly S Up W mem md _ H (CO k Hk)).
Qed.

Lemma thread_off_ush : forall segs B ly S Up W mem md a, FSP.ARU segs B ly S Up W mem md ->
ly_T ly <= a < ly_T ly + kThreadObjSize -> off_ush Up a.
Proof.
intros segs B ly S Up W mem md a H Ha.
pose proof (FSP.ARU_ARm segs B ly S Up W mem md H) as M.
pose proof (am_layout B ly S _ M) as LO.
pose proof (lo_img ly LO) as (I0 & I1 & I2 & I3).
pose proof (proj1 (Forall_forall _ _) (lo_app ly LO) (ly_T ly, kThreadObjSize)
  ltac:(unfold owned_extents; cbn [In]; tauto)) as [P1 P2]. cbn [fst snd] in P1, P2.
pose proof ASAN_CEIL_range as [CR _].
assert (DIV0 : 0 <= (fst (ly_img ly) + snd (ly_img ly)) / 8)
  by (apply Z.div_pos; unfold kImgLo in *; lia).
apply (ush_free_off segs B ly S Up W mem md a H).
- unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
- unfold ush_free, shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *.
  destruct P2 as [P2|[P2 P3]]; [left; lia | right; lia].
Qed.

Lemma high_off_ush : forall segs B ly S Up W mem md a, FSP.ARU segs B ly S Up W mem md ->
kHighMemBeg <= a < 2 ^ 64 -> off_ush Up a.
Proof.
intros segs B ly S Up W mem md a H Ha. apply (ush_free_off segs B ly S Up W mem md a H).
- unfold kHighMemBeg in *. lia.
- right. lia.
Qed.

Lemma low_off_ush : forall segs B ly S Up W mem md a, FSP.ARU segs B ly S Up W mem md ->
0 <= a < SHADOW_OFF -> off_ush Up a.
Proof.
intros segs B ly S Up W mem md a H Ha.
pose proof (FSP.ARU_ARm segs B ly S Up W mem md H) as M.
pose proof (am_layout B ly S _ M) as LO.
pose proof (lo_img ly LO) as (I0 & I1 & I2 & I3).
assert (DIV0 : 0 <= (fst (ly_img ly) + snd (ly_img ly)) / 8)
  by (apply Z.div_pos; unfold kImgLo in *; lia).
apply (ush_free_off segs B ly S Up W mem md a H).
- unfold SHADOW_OFF in *. lia.
- left. unfold shadow_addr, SHADOW_OFF in *. lia.
Qed.
End geo.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. The two instances, and the image premises.                                                                    *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Section inst. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.

(* The type of the walks' Section Variable [ARX] (AllocG.v, DeallocG.v). *)
Definition ARXt : Type := Z -> alayout -> astate -> world segs -> (word -> option byte) -> Model -> Prop.

(* cgif's instance (AGif1m / DGif1dI: [ARX_cgif B inst .. := inst = TFIB_INST /\ AR ..]). *)
Definition ARX_AR (I : Z) : ARXt :=
fun inst ly S W mem md => inst = I /\ AR segs B ly S W mem md.
(* fuzz_state's instance (lib/A/FSRealloc_inst.v FS_ARX): the same window, the any-user-poison invariant. *)
Definition ARX_ARU (I : Z) (Up : list (Z * Z)) : ARXt :=
fun inst ly S W mem md => inst = I /\ FSP.ARU segs B ly S Up W mem md.

(* The instance object lies below the shadow: a fact of the image's instance window (fs: inst = TFIB_INST,
   lib/A|B/FSupoisonARX.fs_inst_low).  Every instance cell the records name is at inst + o with o < 0xe60. *)
Definition inst_low (inst_ok : Z -> Prop) : Prop := forall inst, inst_ok inst -> 0 <= inst /\ inst + 0xe60 <= SHADOW_OFF.

(* A callee's entry zones hold no shadow byte of a live block.  (The consumer reads [ly_img]'s cover off its
   ALedger: al_img puts every segment inside [ly_img], so the image's end bounds the zones' shadow band;
   lib/A|B/FSupoisonARX.fs_zones_free.) *)
Definition zones_free (DZONE CZONE : alayout -> Z -> Prop) : Prop :=
forall ly S W mem md a, AR segs B ly S W mem md -> (DZONE ly a \/ CZONE ly a) ->
0 <= a < 2 ^ 64 /\ ush_free ly a.
End inst.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. The transfer toolkit, shared by the record transfers.                                                         *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Section kit. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- the unpoisoning is pointwise: equalities and visibility move across it at EVERY address ---- *)

Lemma unpoison_eq : forall Up (m m' : word -> option byte) x, m' x = m x -> FSP.unpoison Up m' x = FSP.unpoison Up m x.
Proof. intros Up m m' x E. unfold FSP.unpoison. destruct (FSP.in_ush Up (bv_unsigned x)); [reflexivity | exact E]. Qed.

Lemma aview_unpoison_eq : forall segs (H : word -> bool) Up m m' a, aview segs H m' a = aview segs H m a ->
aview segs H (FSP.unpoison Up m') a = aview segs H (FSP.unpoison Up m) a.
Proof.
intros segs H Up m m' a E. destruct (FSP.in_ush Up (bv_unsigned (Z_to_bv 64 a))) eqn:Ei.
- exact (FSP.aview_unpoison_in segs H Up m' m a Ei).
- rewrite !(FSP.aview_unpoison_out segs H Up _ a Ei). exact E.
Qed.

Lemma aview_unpoison_some : forall segs (H : word -> bool) Up m a, aview segs H m a <> None ->
aview segs H (FSP.unpoison Up m) a <> None.
Proof.
intros segs H Up m a HV. destruct (FSP.in_ush Up (bv_unsigned (Z_to_bv 64 a))) eqn:Ei.
- unfold aview, mbyte, mrestrict in *. destruct (H (Z_to_bv 64 a)); [exact HV|].
  rewrite (FSP.unpoison_in Up m _ Ei). discriminate.
- rewrite (FSP.aview_unpoison_out segs H Up m a Ei). exact HV.
Qed.

(* ---- where a user-poisoned byte can be ---- *)

Lemma ush_band : forall segs B ly S Up W mem md s, FSP.ARU segs B ly S Up W mem md -> FSP.in_ush Up s = true ->
SHADOW_OFF <= shadow_addr (fst (ly_img ly) + snd (ly_img ly)) <= s /\ s < kHighMemBeg /\ 0 <= s < 2 ^ 64.
Proof.
intros segs B ly S Up W mem md s H Hs.
pose proof (ush_lo segs B ly S Up W mem md s H Hs) as [L1 L2].
pose proof (FSP.ARU_ARm segs B ly S Up W mem md H) as M.
pose proof (lo_img ly (am_layout B ly S _ M)) as (I0 & I1 & _).
pose proof (Z.div_pos (fst (ly_img ly) + snd (ly_img ly)) 8 ltac:(unfold kImgLo in *; lia) ltac:(lia)) as D.
unfold shadow_addr in *. unfold kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

Lemma in_ush_w64 : forall segs B ly S Up W mem md s, FSP.ARU segs B ly S Up W mem md -> FSP.in_ush Up s = true ->
bv_unsigned (Z_to_bv 64 s) = s.
Proof. intros segs B ly S Up W mem md s H Hs. pose proof (ush_band segs B ly S Up W mem md s H Hs) as (_ & _ & R). exact (wz64 s R). Qed.

(* Every address of an owned extent, of a secondary map and of the stack is off Up (application memory). *)
Lemma owned_ext_off_ush : forall segs B ly S Up W mem md e a, FSP.ARU segs B ly S Up W mem md ->
In e (owned_extents ly) -> fst e <= a < fst e + snd e -> off_ush Up a.
Proof.
intros segs B ly S Up W mem md e a H He Ha.
pose proof (am_layout B ly S _ (FSP.ARU_ARm segs B ly S Up W mem md H)) as LO.
pose proof (lo_img ly LO) as (I0 & I1 & I2 & I3).
pose proof (proj1 (Forall_forall _ _) (lo_app ly LO) e He) as [P1 P2].
pose proof ASAN_CEIL_range as [CR _].
assert (DIV0 : 0 <= (fst (ly_img ly) + snd (ly_img ly)) / 8) by (apply Z.div_pos; unfold kImgLo in *; lia).
apply (ush_free_off segs B ly S Up W mem md a H).
- unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. destruct P2 as [P2|[P2 P3]]; lia.
- unfold ush_free, shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *.
  destruct P2 as [P2|[P2 P3]]; [left; lia | right; lia].
Qed.

Lemma sec_off_ush : forall segs B ly S Up W mem md e a, FSP.ARU segs B ly S Up W mem md ->
In e (sec_extents ly S) -> fst e <= a < fst e + snd e -> off_ush Up a.
Proof.
intros segs B ly S Up W mem md e a H He Ha.
pose proof (FSP.ARU_ARm segs B ly S Up W mem md H) as M.
pose proof (am_layout B ly S _ M) as LO.
pose proof (am_placed B ly S _ M) as [PL _].
pose proof (lo_img ly LO) as (I0 & I1 & I2 & I3).
pose proof (proj1 (Forall_forall _ _) PL e He) as (_ & [P1 P2] & _).
pose proof ASAN_CEIL_range as [CR _].
assert (DIV0 : 0 <= (fst (ly_img ly) + snd (ly_img ly)) / 8) by (apply Z.div_pos; unfold kImgLo in *; lia).
apply (ush_free_off segs B ly S Up W mem md a H).
- unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. destruct P2 as [P2|[P2 P3]]; lia.
- unfold ush_free, shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *.
  destruct P2 as [P2|[P2 P3]]; [left; lia | right; lia].
Qed.

Lemma stack_off_ush : forall segs B ly S Up W mem md a, FSP.ARU segs B ly S Up W mem md ->
ly_stk_lo ly <= a < ly_stk_hi ly -> off_ush Up a.
Proof.
intros segs B ly S Up W mem md a H Ha.
pose proof (FSP.stk_kHighMemBeg B ly S _ (FSP.ARU_ARm segs B ly S Up W mem md H)) as [K1 K2].
apply (high_off_ush segs B ly S Up W mem md a H). unfold kHighMemBeg, kHighMemEnd in *. lia.
Qed.

(* ---- the two instances ---- *)

Lemma ARX_ARU_AR : forall segs B I Up inst ly S W mem md, ARX_ARU segs B I Up inst ly S W mem md ->
ARX_AR segs B I inst ly S W (FSP.unpoison Up mem) md.
Proof. intros segs B I Up inst ly S W mem md [E H]. exact (conj E (FSP.ARU_AR segs B ly S Up W mem md H)). Qed.

(* ARU after a step: AR at the post over the unpoisoned post memory, every block that holds a range of Up still
   live, and Up's shadow bytes read as before. *)
Lemma ARU_rebuild : forall segs B ly S Up W mem md ly' S' W' mem' md',
FSP.ARU segs B ly S Up W mem md ->
AR segs B ly' S' W' (FSP.unpoison Up mem') md' ->
(forall r p n, In r Up -> In (p, n) (ablocks B ly S) -> p <= fst r -> fst r + snd r <= p + 8 * (req_size n / 8) ->
   In (p, n) (ablocks B ly' S')) ->
(forall s, FSP.in_ush Up s = true -> aview segs (w_H W') mem' s = aview segs (w_H W) mem s) ->
FSP.ARU segs B ly' S' Up W' mem' md'.
Proof.
intros segs B ly S Up W mem md ly' S' W' mem' md' (_ & [FA PW] & PO) HAR BLK VIEW.
split; [exact HAR|]. split.
- split; [|exact PW]. apply Forall_forall. intros r Hr.
  destruct (proj1 (Forall_forall _ _) FA r Hr) as (A1 & A2 & A3 & p & n & Hb & P1 & P2).
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
  exists p, n. split; [exact (BLK r p n Hr Hb P1 P2)|]. split; [exact P1 | exact P2].
- intros s Hs. rewrite (VIEW s Hs). exact (PO s Hs).
Qed.

(* The same, when the world is unchanged and Up's shadow bytes are unchanged in the raw memory. *)
Lemma ARU_rebuild_raw : forall segs B ly S Up W mem md ly' S' mem' md',
FSP.ARU segs B ly S Up W mem md ->
AR segs B ly' S' W (FSP.unpoison Up mem') md' ->
(forall r p n, In r Up -> In (p, n) (ablocks B ly S) -> p <= fst r -> fst r + snd r <= p + 8 * (req_size n / 8) ->
   In (p, n) (ablocks B ly' S')) ->
(forall s, FSP.in_ush Up s = true -> mem' (Z_to_bv 64 s) = mem (Z_to_bv 64 s)) ->
FSP.ARU segs B ly' S' Up W mem' md'.
Proof.
intros segs B ly S Up W mem md ly' S' mem' md' H HAR BLK RAW.
apply (ARU_rebuild segs B ly S Up W mem md ly' S' W mem' md' H HAR BLK).
intros s Hs. exact (FSP.aview_at segs (w_H W) mem' mem s (RAW s Hs)).
Qed.

(* Deallocate's range premise on the ARU side: no range of Up meets the released block (lib/A/FSRealloc_inst.v
   FS_fpre is [fpreU tfibsegs B Up], convertibly). *)
Definition fpreU (segs : list Segment) (B : asyms) (Up : list (Z * Z)) (ly : alayout) (S : astate) (W : world segs)
(mem : word -> option byte) (p : sptr) (n : Z) : Prop :=
forall r, In r Up -> fst r + snd r <= sptr_addr B ly p \/ sptr_addr B ly p + req_size n <= fst r.

End kit.

(* The image's data cells the records name, below the shadow (fs: TFIB_OOM 0x12a1a0, TFIB_ERRNO 0x5dae8c on A,
   AF0m.v:19 / :21). *)
Definition img_low {IM : AImg} : Prop := 0 <= im_oom < SHADOW_OFF /\ 0 <= im_errno /\ im_errno + 4 <= SHADOW_OFF.
