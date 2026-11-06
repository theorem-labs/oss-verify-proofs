(* The AR -> ARU transfer of a Theorem Labs lane's frozen SECONDARY allocator interface record AGif4.AIfaceS (a Theorem Labs lane;
   rule 24: no function proved, kind: statement transfer of an interface record).

   [ifaceS_U]: if cgif's instance [ARX_AR im_segs B I] (inst = I /\ AR) satisfies AIfaceS, fuzz_state's instance
   [ARX_ARU im_segs B I Up] (inst = I /\ FSupoison.ARU .. Up .., the poison set Up fixed outside the call) satisfies it,
   with AOX := [aowned B] on both sides and every other record parameter (U, mt, rpre, nmax, lmax, lpost, dpost, mtag,
   stag) the same variable on both sides.  AIfaceS has no instance field, so the instance window is the premise on I.

   The file is image-free: it Requires lib/Reusable files, lib/A/FSupoison and the toolkit lib/A/FSupoisonARXm only.
   The image enters through the classes ImgBase.AImg / ImgBaseAGS.AImgS and through these premises, each discharged
   by the fs fact named beside it:
   - [inst_low (fun i => i = I)]: I = TFIB_INST, lib/A|B/FSupoisonARX.fs_inst_low.
   - [ims_shb = SHADOW_OFF]: fs's AImgS instance takes ASan's shadow offset 0x7fff8000, as cgif's AGif4cgif.AImgS_cgif
     takes AGjm.SHBv = 0x7fff8000.
   - [zones_free im_segs B ims_dzone (fun ly a => CZS ly I a)]: [zones_free_CZS] below, by the zone's shape: the image
     part of CZS lies below the shadow, its shadow window below the shadow of the image's end (the image ledger,
     lib/A|B/FSupoisonARX.fs_img_end), the thread / context / D cells in owned extents; the depot zone by
     lib/A|B/FSupoisonARX.fs_zones_free.
   - [img_low]: TFIB_OOM 0x12a1a0, TFIB_ERRNO 0x5dae8c (A, AF0m.v), B's YF0m likewise.
   - [zone3_app]: fs's grant zones are lib/A/AF0x.zone3 (B: lib/B/YF0x.zone3), the copies of cgif's YF0x.zone3 that
     cgif's AImgS instance takes (ims_zone3 := zone3): zone3's own conjuncts give 4096 <= x and x + sz <= ASAN_CEIL, and
     each arm of zone3cases lies below kLowShadowBeg (TFIB_IMG_LO = 0x10000, TFIB_IMG_END <= x /\ x + sz <=
     kLowShadowBeg) or at/above kHighMemBeg.
   - [wframe_up ims_wframe]: fs's entry frame is AGif0n.wframe, the image-free copy of AGif0cgif.wframe that cgif's
     AImgS instance takes (ims_wframe := AGif0cgif.wframe); [wframe_up_AGif0n] below proves the premise for it.
   - [nmax <= MALLOC_MAX]: fs instantiates nmax := MALLOC_MAX, as cgif does (cgif AGif5.v:1148, ifaceS_cgif); the walk's
     top asks it of every consumer (cgif AGio.v:66, Hnmax).  The posts need it: ifs_apart's size premise
     (sz <= MALLOC_MAX + 4 * 4096) at the block's map size, and the by_size_log slot (WINI's BSLv) inside the instance
     object.

   How each field transfers (the kinds of the lane's method):
   - ifs_shape (no ARX): verbatim.
   - ifs_fresh, ifs_mwf, ifs_room, ifs_ledger, ifs_grant, ifs_oom (kind 1): the AR field at [unpoison Up mem].
   - ifs_view (kind 2): the AR view over [unpoison Up mem], each clause moved back to [mem]: instance cells below the
     shadow (inst_low), thread cells, the committed pointer array (an owned extent), const cells (owned core).
   - ifs_depot (kind 3): the entry memory replaced by [unpoison Up mem0]; its zones are off Up by [zones_free].
   - ifs_apart (kind 2): the AR field; a granule of a fresh grant is in no live block (the grant is disjoint from the
     primary reservation, an owned extent, and from every secondary map), so its shadow byte is no Up byte
     (FSP.ARU_shadow_out_block).
   - ifs_post_null, ifs_post_grant (kind 4): the machine post moved to the unpoisoned memories (raw / aview equalities
     pointwise, presence forward, each fixed cell off Up: instance, thread, oom, the pointer-array slot, the new map, the
     new map's shadow); the AR field applied; ARU rebuilt at the post with ARU_rebuild(_raw): every old block keeps its
     address (lyFz changes only the new secondary slot; sfinal appends KS), and each Up byte reads as before (it is
     outside every window the post may write, and it stays visible: it was visible in W, sk_mon).  The frame clauses
     need no machine fact: an address outside [aowned B ly S] is no Up byte (FSP.ush_facts).

   No Axiom, no Admitted. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0b YG0g YG0h YG0j YG0t.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK0v YK13 YP0n YA05 YA09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import ImgBase ImgBaseAGS AGif2 AllocG AGif4.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require AGif0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoisonARXm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.
Fail Definition probe_SH : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI14.sink_syms := _.

Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {IM : AImg} {IMS : AImgS}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. The image premises beyond the toolkit's.                                                                       *)
(* ---------------------------------------------------------------------------------------------------------------- *)

(* A kernel grant lies in application memory: below the low shadow or at/above kHighMemBeg (fs: AF0x.zone3). *)
Definition zone3_app : Prop :=
forall x sz, ims_zone3 x sz -> 4096 <= x /\ x + sz <= ASAN_CEIL /\ (x + sz <= kLowShadowBeg \/ kHighMemBeg <= x).

(* The walk's entry frame puts Allocate's stack window in the stack, and it reads the memory only through presence
   on that window, so the unpoisoning keeps it (fs: AGif0n.wframe, [wframe_up_AGif0n]). *)
Definition wframe_up (wf : world im_segs -> alayout -> bvmap 5 word -> (word -> option byte) -> list Z -> Prop) : Prop :=
forall W ly regs0 mem0 tr, wf W ly regs0 mem0 tr ->
(ly_stk_lo ly + ImgBaseAGS.AFSTACK <= bv_unsigned (getr regs0 2) /\ bv_unsigned (getr regs0 2) <= ly_stk_hi ly) /\
forall Up, wf W ly regs0 (FSP.unpoison Up mem0) tr.

Lemma wframe_up_AGif0n : wframe_up AGif0n.wframe.
Proof.
intros W ly regs0 mem0 tr ((F1 & F2 & F3 & F4) & F5 & F6 & F7 & F8).
split; [split; [exact F1 | exact F3]|].
intros Up. refine (conj (conj F1 (conj F2 (conj F3 F4))) (conj F5 (conj F6 (conj F7 _)))).
intros a Ha. apply apresent_unpoison_fwd. exact (F8 a Ha).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. Where a user-poisoned byte cannot be.                                                                          *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Lemma off_contra : forall Up s, off_ush Up s -> FSP.in_ush Up s = true -> 0 <= s < 2 ^ 64 -> False.
Proof. intros Up s H E R. unfold off_ush in H. rewrite (Z.mod_small s _ R) in H. congruence. Qed.

(* Below the shadow or at/above kHighMemBeg. *)
Lemma band_off : forall segs B ly S Up W mem md a, FSP.ARU segs B ly S Up W mem md -> 0 <= a < 2 ^ 64 ->
a < SHADOW_OFF \/ kHighMemBeg <= a -> off_ush Up a.
Proof.
intros segs B ly S Up W mem md a H R Ha. unfold off_ush. rewrite (Z.mod_small a _ R).
destruct (FSP.in_ush Up a) eqn:E; [|reflexivity]. exfalso.
pose proof (ush_band segs B ly S Up W mem md a H E) as (B1 & B2 & B3). lia.
Qed.

(* An Up byte is owned (FSP.ush_facts): an address the allocator does not own is no Up byte. *)
Lemma noown_off : forall segs B ly S Up W mem md a, FSP.ARU segs B ly S Up W mem md -> 0 <= a < 2 ^ 64 ->
~ aowned B ly S a -> off_ush Up a.
Proof.
intros segs B ly S Up W mem md a H R NA. unfold off_ush. rewrite (Z.mod_small a _ R).
destruct (FSP.in_ush Up a) eqn:E; [|reflexivity]. exfalso.
exact (NA (proj1 (FSP.ush_facts segs B ly S Up W mem md a H E))).
Qed.

Lemma noown_off_w : forall segs B ly S Up W mem md (x : word), FSP.ARU segs B ly S Up W mem md ->
~ aowned B ly S (bv_unsigned x) -> FSP.in_ush Up (bv_unsigned x) = false.
Proof.
intros segs B ly S Up W mem md x H NA. apply off_ush_w.
exact (noown_off segs B ly S Up W mem md (bv_unsigned x) H (bv_range64 x) NA).
Qed.

(* A live block lies inside the primary reservation or inside a secondary map of the state. *)
Lemma block_in_extent : forall B ly S rd p m q, ARm B ly S rd -> In (p, m) (ablocks B ly S) -> p <= q < p + req_size m ->
in_zr q (ly_prim ly, kPrimResvSize) \/ exists e, In e (sec_extents ly S) /\ in_zr q e.
Proof.
intros B ly S rd p m q M Hb Hq.
destruct (FSP.ablock_chunk B ly S p m Hb) as (k & Hk & Hu & Hn). subst p m.
pose proof (am_layout B ly S rd M) as LO.
pose proof (chunk_facts B ly S rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
rewrite G4 in Hq.
destruct (ck_beg k) as [|off|r o|c pp] eqn:Eb; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal).
  pose proof (region_in_prim ly (prim_class off) LO ltac:(lia)) as (R1 & R2 & _).
  assert (E32 : 2 ^ 32 = 4294967296) by reflexivity. rewrite E32 in R2.
  unfold kFreeArrayOffset in Gal. left. unfold in_zr. cbn [fst snd]. lia.
- destruct GG as (Go & _ & Gbase & Gext & Gin & _). right.
  exists (ly_sec ly r, sec_map_size (ck_req k)). split; [exact Gin|]. unfold in_zr. cbn [fst snd]. unfold kPage in *. lia.
Qed.

(* A point of a grant disjoint from the static extents and the secondary maps is in no live block. *)
Lemma grant_no_block : forall B ly S rd a sz q, ARm B ly S rd ->
Forall (zdisjoint (a, sz)) (static_extents ly ++ vis0_zones ly ++ sec_extents ly S) -> a <= q < a + sz ->
forall p m, In (p, m) (ablocks B ly S) -> ~ (p <= q < p + req_size m).
Proof.
intros B ly S rd a sz q M DJ Hq p m Hb Hpq.
destruct (block_in_extent B ly S rd p m q M Hb Hpq) as [HP | (e & He & HE)].
- assert (IN : In (ly_prim ly, kPrimResvSize) (static_extents ly ++ vis0_zones ly ++ sec_extents ly S)).
  { apply in_or_app. left. unfold static_extents. apply in_or_app. left. unfold owned_extents. left. reflexivity. }
  pose proof (proj1 (Forall_forall _ _) DJ _ IN) as D. unfold zdisjoint in D. unfold in_zr in HP.
  cbn [fst snd] in D, HP. lia.
- assert (IN : In e (static_extents ly ++ vis0_zones ly ++ sec_extents ly S)).
  { apply in_or_app. right. apply in_or_app. right. exact He. }
  pose proof (proj1 (Forall_forall _ _) DJ _ IN) as D. unfold zdisjoint in D. unfold in_zr in HE.
  cbn [fst snd] in D. lia.
Qed.

(* The shadow of such a grant holds no Up byte. *)
Lemma grant_shadow_off : forall segs B ly S Up W mem md a sz x, FSP.ARU segs B ly S Up W mem md ->
Forall (zdisjoint (a, sz)) (static_extents ly ++ vis0_zones ly ++ sec_extents ly S) ->
SHADOW_OFF + a / 8 <= x < SHADOW_OFF + a / 8 + sz / 8 -> 0 <= x < 2 ^ 64 -> off_ush Up x.
Proof.
intros segs B ly S Up W mem md a sz x H DJ Hx R. unfold off_ush. rewrite (Z.mod_small x _ R).
destruct (FSP.in_ush Up x) eqn:E; [|reflexivity]. exfalso.
destruct (FSP.ush_granule B ly S Up x (FSP.ARU_ok segs B ly S Up W mem md H) E) as (g & p & m & Hb & G8 & Gs & Gp & Gm).
unfold shadow_addr in Gs.
pose proof (Z.mul_div_le (req_size m) 8 ltac:(lia)) as RD.
pose proof (Z.div_mod a 8 ltac:(lia)) as DA. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as MA.
pose proof (Z.div_mod sz 8 ltac:(lia)) as DS. pose proof (Z.mod_pos_bound sz 8 ltac:(lia)) as MS.
pose proof (Z.div_mod g 8 ltac:(lia)) as DG.
apply (grant_no_block B ly S _ a sz (Z.max g a) (FSP.ARU_ARm segs B ly S Up W mem md H) DJ ltac:(lia) p m Hb).
lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. The secondary block's geometry, as the windows need it.                                                       *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Lemma MSv_facts : forall n, 0 <= n -> n + 8192 <= ImgBaseAGS.MSv n <= n + 12294 /\ ImgBaseAGS.MSv n mod 4096 = 0.
Proof.
intros n Hn. unfold ImgBaseAGS.MSv, ImgBaseAGS.NDv, ImgBaseAGS.R8v.
pose proof (Z.div_mod (n + 7) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod ((n + 7) / 8 * 8 + 4096 + 4095) 4096 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound ((n + 7) / 8 * 8 + 4096 + 4095) 4096 ltac:(lia)) as M2.
split; [lia|].
replace (((n + 7) / 8 * 8 + 4096 + 4095) / 4096 * 4096 + 4096)
  with ((((n + 7) / 8 * 8 + 4096 + 4095) / 4096 + 1) * 4096) by ring.
apply Z.mod_mul. lia.
Qed.

(* The by_size_log slot index of a size below MALLOC_MAX. *)
Lemma LGv_le : forall n, 0 <= n < MALLOC_MAX -> 12 <= ImgBaseAGS.LGv n <= 29.
Proof.
intros n Hn. pose proof (MSv_facts n ltac:(lia)) as [M1 M2]. unfold ImgBaseAGS.LGv.
pose proof (Z.log2_nonneg (ImgBaseAGS.MSv n / 4096)) as L0.
assert (D : ImgBaseAGS.MSv n / 4096 <= 2 ^ 17).
{ apply Z.div_le_upper_bound; [lia|]. change (4096 * 2 ^ 17) with 536870912.
  unfold MALLOC_MAX in Hn. change (2 ^ 28) with 268435456 in Hn. lia. }
pose proof (Z.log2_le_mono _ _ D) as L. rewrite Z.log2_pow2 in L by lia. lia.
Qed.

(* Every byte of WINI is a byte of the instance object. *)
Lemma WINI_inst : forall regs0 n I a, bv_unsigned (getr regs0 11) = I -> 0 <= n < MALLOC_MAX ->
ImgBaseAGS.WINI regs0 n a -> I <= a < I + 0xe60.
Proof.
intros regs0 n I a E Hn HW. pose proof (LGv_le n Hn) as L.
unfold ImgBaseAGS.WINI, ImgBaseAGS.BSLv in HW. cbv zeta in HW. rewrite E in HW.
unfold o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, o_comb_stats in HW. lia.
Qed.

(* Every byte of WINT is a byte of the thread object. *)
Lemma WINT_thread : forall ly a, ImgBaseAGS.WINT ly a -> ly_T ly <= a < ly_T ly + kThreadObjSize.
Proof.
intros ly a H. unfold ImgBaseAGS.WINT in H. cbv zeta in H. unfold t_unwinding, kThreadObjSize in *.
destruct H as [H | [H | [H | H]]]; lia.
Qed.

(* The grant post keeps every old block at its address: lyFz moves only the new secondary slot, sfinal appends KS. *)
Lemma blocks_keep : forall B ly S rd mb n tr z grow p m, ARm B ly S rd -> In (p, m) (ablocks B ly S) ->
In (p, m) (ablocks B (lyFz ly S mb) (SFSz S n tr z grow)).
Proof.
intros B ly S rd mb n tr z grow p m M Hin.
unfold ablocks in *. apply in_map_iff in Hin as ([q mm] & Eq & Hin2).
unfold blocks in Hin2. apply in_map_iff in Hin2 as (k & Ek & Hk). apply filter_In in Hk as [Hk Hal].
apply in_map_iff. exists (q, mm). split.
- rewrite <- Eq. cbn [fst snd]. injection Ek as Eq1 Eq2. subst q mm. f_equal.
  pose proof (chunk_facts B ly S rd k M Hk) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
  unfold ck_user, lyFz, set_ly_sec, ImgBaseAGS.rS, sptr_addr.
  destruct (ck_beg k) as [|off|r o|c pp]; try solve [destruct GG].
  + cbn. reflexivity.
  + destruct GG as (_ & _ & _ & _ & _ & _ & Glt). cbn [padd sptr_exp aeval ly_sec].
    destruct (Nat.eqb_spec r (length (st_secs S))); [lia | reflexivity].
- unfold blocks. apply in_map_iff. exists k. split; [exact Ek|]. apply filter_In. split; [|exact Hal].
  unfold SFSz, ImgBaseAGS.sfinal. cbn [st_chunks]. apply in_or_app. left. exact Hk.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. The view and the machine posts across the unpoisoning.                                                        *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Lemma sview_U : forall B ly S W mem md inst Up idx res, FSP.ARU im_segs B ly S Up W mem md ->
(forall a, inst <= a < inst + 0xe60 -> off_ush Up a) ->
sview B W ly inst (FSP.unpoison Up mem) idx res -> sview B W ly inst mem idx res.
Proof.
intros B ly S W mem md inst Up idx res H OFFI [L1 L2 L3 C V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 VU TP SP CP QA IX RB].
assert (VM : forall a w v, (forall k, 0 <= k < Z.of_nat w -> off_ush Up (a + k)) ->
  val_mem im_segs (mrestrict (w_H W) (FSP.unpoison Up mem)) a w v -> val_mem im_segs (mrestrict (w_H W) mem) a w v)
  by (intros a w v HO HV; exact (proj1 (val_mem_unpoison im_segs (w_H W) Up mem a w v HO) HV)).
assert (OFFT : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> off_ush Up a)
  by (intros a Ha; exact (thread_off_ush im_segs B ly S Up W mem md a H Ha)).
constructor.
- exact L1.
- exact L2.
- exact L3.
- apply Forall_forall. intros c Hc. apply (cell_holds_unpoison im_segs B ly (w_H W) Up mem c).
  + intros k Hk. exact (const_cell_off_ush im_segs B ly S Up W mem md c H Hc k Hk).
  + exact (proj1 (Forall_forall _ _) C c Hc).
- apply VM; [intros k Hk; apply OFFI; unfold o_space; lia | exact V1].
- apply VM; [intros k Hk; apply OFFI; lia | exact V2].
- apply VM; [intros k Hk; apply OFFI; lia | exact V3].
- apply VM; [intros k Hk; apply OFFI; unfold o_sec; lia | exact V4].
- apply VM; [intros k Hk; apply OFFI; unfold o_sec_chunks; lia | exact V5].
- apply VM; [intros k Hk; apply OFFI; lia | exact V6].
- apply VM; [intros k Hk; apply OFFI; lia | exact V7].
- apply VM; [intros k Hk; apply OFFI; unfold o_sec_reserved; lia | exact V8].
- apply VM; [intros k Hk; apply OFFI; unfold o_sec_n; lia | exact V9].
- apply VM; [intros k Hk; apply OFFI; unfold o_sec_mutex; lia | exact V10].
- apply VM; [intros k Hk; apply OFFT; unfold t_unwinding, kThreadObjSize; lia | exact VU].
- intros a Ha. apply (apresent_unpoison_bwd (w_H W) Up mem a); [|exact (TP a Ha)].
  apply OFFT. unfold t_cache_stats, t_unwinding, kThreadObjSize in *. lia.
- intros a Ha. rewrite <- (aview_unpoison_off im_segs (w_H W) Up mem a); [exact (SP a Ha)|].
  apply OFFI. unfold o_sec_stats, o_sec_mutex in *. lia.
- intros a Ha. rewrite <- (aview_unpoison_off im_segs (w_H W) Up mem a); [exact (CP a Ha)|].
  apply OFFI. unfold o_comb_stats in *. lia.
- intros a Ha. apply (apresent_unpoison_bwd (w_H W) Up mem a); [|exact (QA a Ha)].
  apply (owned_ext_off_ush im_segs B ly S Up W mem md (ly_Q ly, kPtrArrayResv) a H);
  [unfold owned_extents; cbn [In]; tauto |].
  cbn [fst snd]. destruct RB as [[RB1 RB2] _]. unfold kMaxNumChunks, kPtrArrayResv in *. lia.
- exact IX.
- exact RB.
Qed.

Lemma snull_U : forall W ly regs0 mem0 inst n idx res mb regs' mem' Up,
(forall a, inst <= a < inst + 0xe60 -> off_ush Up a) ->
(forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> off_ush Up a) ->
off_ush Up im_oom ->
snull W ly regs0 mem0 inst n idx res mb regs' mem' ->
snull W ly regs0 (FSP.unpoison Up mem0) inst n idx res mb regs' (FSP.unpoison Up mem').
Proof.
intros W ly regs0 mem0 inst n idx res mb regs' mem' Up OFFI OFFT OOM
  [R10 RCS MEQ PRS PRW VISI Voom Vunw Vres Vnch Vmtx].
assert (VM : forall a w v, (forall k, 0 <= k < Z.of_nat w -> off_ush Up (a + k)) ->
  val_mem im_segs (mrestrict (w_H W) mem') a w v -> val_mem im_segs (mrestrict (w_H W) (FSP.unpoison Up mem')) a w v)
  by (intros a w v HO HV; exact (proj2 (val_mem_unpoison im_segs (w_H W) Up mem' a w v HO) HV)).
constructor.
- exact R10.
- exact RCS.
- intros x H1 H2 H3. apply unpoison_eq. exact (MEQ x H1 H2 H3).
- intros a Ha. apply apresent_unpoison_fwd. exact (PRS a Ha).
- intros a Ha. apply apresent_unpoison_fwd. exact (PRW a Ha).
- intros a Ha. apply aview_unpoison_some. exact (VISI a Ha).
- apply VM; [intros k Hk; replace (im_oom + k) with im_oom by lia; exact OOM | exact Voom].
- apply VM; [intros k Hk; apply OFFT; unfold t_unwinding, kThreadObjSize; lia | exact Vunw].
- apply VM; [intros k Hk; apply OFFI; unfold o_sec_reserved; lia | exact Vres].
- apply VM; [intros k Hk; apply OFFI; unfold o_sec_n; lia | exact Vnch].
- apply VM; [intros k Hk; apply OFFI; unfold o_sec_mutex; lia | exact Vmtx].
Qed.

Lemma sfin_U : forall W ly regs0 mem0 inst n tr idx res mb DPOST grow z Wz regs' mem' Up,
64513 <= n ->
(forall a, ims_dzone ly a -> off_ush Up a) ->
(forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> off_ush Up a) ->
(forall a, inst <= a < inst + 0xe60 -> off_ush Up a) ->
(forall a, ImgBaseAGS.QSv ly idx <= a < ImgBaseAGS.QSv ly idx + 8 -> off_ush Up a) ->
(forall a, mb <= a < mb + ImgBaseAGS.MSv n -> off_ush Up a) ->
(forall a, ImgBaseAGS.SMv mb <= a < ImgBaseAGS.SMv mb + ImgBaseAGS.MSv n / 8 -> off_ush Up a) ->
sfin W ly regs0 mem0 inst n tr idx res mb DPOST grow z Wz regs' mem' ->
sfin W ly regs0 (FSP.unpoison Up mem0) inst n tr idx res mb DPOST grow z Wz regs' (FSP.unpoison Up mem').
Proof.
intros W ly regs0 mem0 inst n tr idx res mb DPOST grow z Wz regs' mem' Up Hn OFFZ OFFT OFFI OFFQ OFFM OFFMS
  [Dep MEQF PRS PRmap PRsh PRq PRW VISW R10 RCS Vsh Vzs Vpb Vunw Vres Vnch Vmtx Vpad Vslot
   Vh0 Vh8 Vh16 Vh24 Vmag Vbk Vst Vb1 Vb2 Vn Vfill].
pose proof (MSv_facts n ltac:(lia)) as [MS1 MS2].
assert (VM : forall a w v, (forall k, 0 <= k < Z.of_nat w -> off_ush Up (a + k)) ->
  val_mem im_segs (mrestrict (w_H Wz) mem') a w v -> val_mem im_segs (mrestrict (w_H Wz) (FSP.unpoison Up mem')) a w v)
  by (intros a w v HO HV; exact (proj2 (val_mem_unpoison im_segs (w_H Wz) Up mem' a w v HO) HV)).
assert (D1 : 1024 + n / 8 <= ImgBaseAGS.MSv n / 8).
{ assert (E : (n + 1024 * 8) / 8 = n / 8 + 1024) by (rewrite Z.div_add by lia; lia).
  pose proof (Z.div_le_mono (n + 1024 * 8) (ImgBaseAGS.MSv n) 8 ltac:(lia) ltac:(lia)). lia. }
assert (D2 : mb / 8 <= ImgBaseAGS.UEv n mb / 8).
{ apply Z.div_le_mono; [lia|]. unfold ImgBaseAGS.UEv, ImgBaseAGS.R8v.
  pose proof (Z.div_pos (n + 7) 8 ltac:(lia) ltac:(lia)). lia. }
assert (D3 : ImgBaseAGS.N8D n / 8 = n / 8) by (unfold ImgBaseAGS.N8D; apply Z.div_mul; lia).
assert (D4 : (mb + 6144 + ImgBaseAGS.N8D n) / 8 = mb / 8 + 768 + n / 8).
{ unfold ImgBaseAGS.N8D. replace (mb + 6144 + n / 8 * 8) with (mb + (768 + n / 8) * 8) by ring.
  rewrite Z.div_add by lia. lia. }
pose proof (Z.div_pos n 8 ltac:(lia) ltac:(lia)) as D5.
constructor.
- destruct Dep as (memD & DD1 & DD2 & DD3). exists memD. split; [exact DD1|]. split.
  + intros a Ha HP. exact (DD2 a Ha (apresent_unpoison_bwd (w_H Wz) Up mem0 a (OFFZ a Ha) HP)).
  + intros x Hx. rewrite (FSP.unpoison_out Up mem' x (off_ush_w Up x (OFFZ _ Hx))). exact (DD3 x Hx).
- intros x H1 H2 H3. apply unpoison_eq. exact (MEQF x H1 H2 H3).
- intros a Ha. apply apresent_unpoison_fwd. exact (PRS a Ha).
- intros a Ha. apply apresent_unpoison_fwd. exact (PRmap a Ha).
- intros a Ha. apply apresent_unpoison_fwd. exact (PRsh a Ha).
- intros Hg a Ha. apply apresent_unpoison_fwd. exact (PRq Hg a Ha).
- intros a Ha. apply apresent_unpoison_fwd. exact (PRW a Ha).
- intros a Ha. apply aview_unpoison_some. exact (VISW a Ha).
- exact R10.
- exact RCS.
- intros x Hx. assert (Hx' : ImgBaseAGS.SMv mb <= bv_unsigned x < ImgBaseAGS.SMv mb + ImgBaseAGS.MSv n / 8)
    by (unfold ImgBaseAGS.SMv in *; destruct Hx as [Hx | Hx]; lia).
  rewrite (FSP.unpoison_out Up mem' x (off_ush_w Up x (OFFMS (bv_unsigned x) Hx'))). exact (Vsh x Hx).
- intros x Hx. assert (Hx' : ImgBaseAGS.SMv mb <= bv_unsigned x < ImgBaseAGS.SMv mb + ImgBaseAGS.MSv n / 8) by lia.
  rewrite (FSP.unpoison_out Up mem' x (off_ush_w Up x (OFFMS (bv_unsigned x) Hx'))). exact (Vzs x Hx).
- intros Hodd. apply VM; [|exact (Vpb Hodd)]. intros k Hk. apply OFFMS.
  unfold ImgBaseAGS.PBv, ImgBaseAGS.SMv. rewrite D4. lia.
- apply VM; [intros k Hk; apply OFFT; unfold t_unwinding, kThreadObjSize; lia | exact Vunw].
- apply VM; [intros k Hk; apply OFFI; unfold o_sec_reserved; lia | exact Vres].
- apply VM; [intros k Hk; apply OFFI; unfold o_sec_n; lia | exact Vnch].
- apply VM; [intros k Hk; apply OFFI; unfold o_sec_mutex; lia | exact Vmtx].
- intros k Hk. assert (Hk' : inst <= inst + o_sec_mutex + k < inst + 0xe60) by (unfold o_sec_mutex; lia).
  rewrite (aview_unpoison_off im_segs (w_H Wz) Up mem' _ (OFFI _ Hk')). exact (Vpad k Hk).
- apply VM; [intros k Hk; apply OFFQ; lia | exact Vslot].
- apply VM; [intros k Hk; apply OFFM; lia | exact Vh0].
- apply VM; [intros k Hk; apply OFFM; lia | exact Vh8].
- apply VM; [intros k Hk; apply OFFM; lia | exact Vh16].
- apply VM; [intros k Hk; apply OFFM; lia | exact Vh24].
- apply VM; [intros k Hk; apply OFFM; unfold ImgBaseAGS.Kv; lia | exact Vmag].
- apply VM; [intros k Hk; apply OFFM; unfold ImgBaseAGS.Kv; lia | exact Vbk].
- apply VM; [intros k Hk; apply OFFM; unfold ImgBaseAGS.Uv; lia | exact Vst].
- apply VM; [intros k Hk; apply OFFM; unfold ImgBaseAGS.Uv; lia | exact Vb1].
- apply VM; [intros k Hk; apply OFFM; unfold ImgBaseAGS.Uv; lia | exact Vb2].
- apply VM; [intros k Hk; apply OFFM; unfold ImgBaseAGS.Uv; lia | exact Vn].
- intros Hcf x Hx. assert (Hx' : mb <= bv_unsigned x < mb + ImgBaseAGS.MSv n) by (unfold ImgBaseAGS.Uv in *; lia).
  rewrite (FSP.unpoison_out Up mem' x (off_ush_w Up x (OFFM (bv_unsigned x) Hx'))). exact (Vfill Hcf x Hx).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 5. The record.                                                                                                    *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Theorem ifaceS_U : forall B U mt rpre nmax lmax lpost dpost mtag stag I Up,
inst_low (fun i => i = I) -> ims_shb = SHADOW_OFF -> zones_free im_segs B ims_dzone (fun ly a => CZS ly I a) -> img_low ->
zone3_app -> wframe_up ims_wframe -> nmax <= MALLOC_MAX ->
AIfaceS B U mt (ARX_AR im_segs B I) (aowned B) rpre nmax lmax lpost dpost mtag stag ->
AIfaceS B U mt (ARX_ARU im_segs B I Up) (aowned B) rpre nmax lmax lpost dpost mtag stag.
Proof.
intros B U mt rpre nmax lmax lpost dpost mtag stag I Up ILOW SHB ZON IMGL ZN3 WFU NMAX
  [Fview Fshape Ffresh Fdepot Fmwf Froom Fledger Fgrant Fapart Foom Fnull Fpost].
destruct (ILOW I eq_refl) as [IL0 IL1].
destruct IMGL as (OOM1 & ER1 & ER2).
assert (OFFI : forall ly S W mem md a, FSP.ARU im_segs B ly S Up W mem md -> I <= a < I + 0xe60 -> off_ush Up a)
  by (intros ly S W mem md a H Ha; apply (band_off im_segs B ly S Up W mem md a H); unfold SHADOW_OFF in *; lia).
assert (I11 : forall regs0 : bvmap 5 word, getr regs0 11 = w64 I -> bv_unsigned (getr regs0 11) = I)
  by (intros regs0 H11; rewrite H11; exact (wz64 I ltac:(unfold SHADOW_OFF in *; lia))).
constructor.
- (* ifs_view *)
  intros inst ly S W mem md n [E HARU] Hr Hn. subst inst.
  apply (sview_U B ly S W mem md I Up _ _ HARU (fun a => OFFI ly S W mem md a HARU)).
  exact (Fview I ly S W (FSP.unpoison Up mem) md n (conj eq_refl (FSP.ARU_AR _ _ _ _ _ _ _ _ HARU)) Hr Hn).
- (* ifs_shape *)
  exact Fshape.
- (* ifs_fresh *)
  intros inst ly S W mem md H. exact (Ffresh inst ly S W _ md (ARX_ARU_AR im_segs B I Up inst ly S W mem md H)).
- (* ifs_depot *)
  intros inst ly S W mem0 md0 tr Wy regs mem md buf [E HARU] HU HW HZ. subst inst.
  pose proof (FSP.ARU_AR _ _ _ _ _ _ _ _ HARU) as HAR.
  refine (Fdepot I ly S W (FSP.unpoison Up mem0) md0 tr Wy regs mem md buf (conj eq_refl HAR) HU HW _).
  intros x Hx. destruct (ZON ly S W (FSP.unpoison Up mem0) md0 (bv_unsigned x) HAR Hx) as [HR HF].
  rewrite (FSP.unpoison_out Up mem0 x
    (off_ush_w Up x (ush_free_off im_segs B ly S Up W mem0 md0 (bv_unsigned x) HARU HR HF))).
  exact (HZ x Hx).
- (* ifs_mwf *)
  intros inst ly S W mem md H. exact (Fmwf inst ly S W _ md (ARX_ARU_AR im_segs B I Up inst ly S W mem md H)).
- (* ifs_room *)
  intros inst ly S W mem md n H Hr. exact (Froom inst ly S W _ md n (ARX_ARU_AR im_segs B I Up inst ly S W mem md H) Hr).
- (* ifs_ledger *)
  intros inst ly S W mem md H. exact (Fledger inst ly S W _ md (ARX_ARU_AR im_segs B I Up inst ly S W mem md H)).
- (* ifs_grant *)
  intros inst ly S W mem md mat sz H Hsz.
  exact (Fgrant inst ly S W _ md mat sz (ARX_ARU_AR im_segs B I Up inst ly S W mem md H) Hsz).
- (* ifs_apart *)
  intros inst ly S W mem md mat sz a [E HARU] Hsz Hm HG. subst inst.
  pose proof (FSP.ARU_AR _ _ _ _ _ _ _ _ HARU) as HAR.
  destruct (Fapart I ly S W (FSP.unpoison Up mem) md mat sz a (conj eq_refl HAR) Hsz Hm HG) as (Z3 & DJ & SH0).
  split; [exact Z3|]. split; [exact DJ|].
  destruct (ZN3 _ _ Z3) as (Z31 & Z32 & _). pose proof ASAN_CEIL_range as [[CR1 CR2] _].
  intros g G8 G1 G2.
  rewrite <- (FSP.unpoison_out Up mem _ (FSP.ARU_shadow_out_block im_segs B ly S Up W mem md g HARU ltac:(lia)
    (grant_no_block B ly S _ (bv_unsigned a) sz g (FSP.ARU_ARm _ _ _ _ _ _ _ _ HARU) DJ ltac:(lia)))).
  exact (SH0 g G8 G1 G2).
- (* ifs_oom *)
  intros inst ly S W mem md H. exact (Foom inst ly S W _ md (ARX_ARU_AR im_segs B I Up inst ly S W mem md H)).
- (* ifs_post_null *)
  intros inst ly S W mem0 md0 n tr regs0 regs' mem' mat [E HARU] Hr Hn Hl HU HWF H11 HSN. subst inst.
  pose proof (FSP.ARU_AR _ _ _ _ _ _ _ _ HARU) as HAR.
  pose proof (FSP.ARU_ARm _ _ _ _ _ _ _ _ HARU) as M.
  destruct (WFU W ly regs0 mem0 tr HWF) as [[SP1 SP2] HWFU].
  pose proof (FSP.stk_kHighMemBeg B ly S _ M) as [SK1 SK2].
  pose proof HSN as [_ _ SNMEQ _ _ _ _ _ _ _ _].
  assert (OFFT : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> off_ush Up a)
    by (intros a Ha; exact (thread_off_ush im_segs B ly S Up W mem0 md0 a HARU Ha)).
  assert (OOMoff : off_ush Up im_oom).
  { apply (band_off im_segs B ly S Up W mem0 md0 im_oom HARU); [|left; exact (proj2 OOM1)].
    pose proof OOM1 as OO. unfold SHADOW_OFF in OO. lia. }
  destruct (Fnull I ly S W (FSP.unpoison Up mem0) md0 n tr regs0 regs' (FSP.unpoison Up mem') mat
    (conj eq_refl HAR) Hr Hn Hl HU (HWFU Up) H11
    (snull_U W ly regs0 mem0 I n _ _ 0 regs' mem' Up (fun a => OFFI ly S W mem0 md0 a HARU) OFFT OOMoff HSN))
    as (HARp & HLp & FRa & FRr).
  split; [|split; [exact HLp|split]].
  + split; [reflexivity|].
    apply (ARU_rebuild_raw im_segs B ly S Up W mem0 md0 ly (set_nev (st_nev S + 1) S) mem' _ HARU (proj2 HARp)).
    * intros r p m _ Hb _ _. exact Hb.
    * intros s Hs. pose proof (ush_band im_segs B ly S Up W mem0 md0 s HARU Hs) as (B1 & B2 & B3).
      apply (SNMEQ (Z_to_bv 64 s)); rewrite (wz64 s B3).
      -- intros HW. unfold ImgBaseAGS.WINP in HW. cbv zeta in HW. destruct HW as [HW | [HW | HW]].
         ++ unfold ImgBaseAGS.AFSTACK in *. lia.
         ++ exact (off_contra Up s (OFFT s (WINT_thread ly s HW)) Hs B3).
         ++ pose proof (WINI_inst regs0 n I s (I11 regs0 H11) ltac:(lia) HW). unfold SHADOW_OFF in *. lia.
      -- lia.
      -- lia.
  + intros a Ha NA NS.
    rewrite <- (aview_unpoison_off im_segs (w_H W) Up mem' a (noown_off im_segs B ly S Up W mem0 md0 a HARU Ha NA)).
    rewrite <- (aview_unpoison_off im_segs (w_H W) Up mem0 a (noown_off im_segs B ly S Up W mem0 md0 a HARU Ha NA)).
    exact (FRa a Ha NA NS).
  + intros x NA NA' NS. pose proof (noown_off_w im_segs B ly S Up W mem0 md0 x HARU NA) as OX.
    rewrite <- (FSP.unpoison_out Up mem' x OX), <- (FSP.unpoison_out Up mem0 x OX). exact (FRr x NA NA' NS).
- (* ifs_post_grant *)
  intros inst ly S W mem0 md0 n tr regs0 mb grow z Wz mdz regs' mem' [E HARU] Hr Hn Hl HU HWF H11 HGROW HSK HSF HAOK.
  subst inst.
  pose proof (FSP.ARU_AR _ _ _ _ _ _ _ _ HARU) as HAR.
  pose proof (FSP.ARU_ARm _ _ _ _ _ _ _ _ HARU) as M.
  destruct (WFU W ly regs0 mem0 tr HWF) as [[SP1 SP2] HWFU].
  pose proof (Fview I ly S W (FSP.unpoison Up mem0) md0 n (conj eq_refl HAR) Hr Hn) as SV.
  pose proof (sv_idx _ _ _ _ _ _ _ SV) as HIDX. pose proof (sv_resb _ _ _ _ _ _ _ SV) as [[HRES1 HRES2] _].
  pose proof (MSv_facts n ltac:(lia)) as [MS1 MS2].
  pose proof HSK as [SKmbr SKmd _ _ _ SKmon _ _ _ _ _ _ _ _].
  destruct SKmd as (mat & matV & matR & Emd & HGOK & _).
  destruct (Fapart I ly S W (FSP.unpoison Up mem0) md0 mat (ImgBaseAGS.MSv n) (w64 mb) (conj eq_refl HAR)
    ltac:(unfold MALLOC_MAX in *; lia) MS2 HGOK) as (Z3 & DJ & _).
  assert (EMB : bv_unsigned (w64 mb) = mb) by exact (wz64 mb SKmbr).
  rewrite EMB in Z3, DJ.
  destruct (ZN3 _ _ Z3) as (Z31 & Z32 & Z33). pose proof ASAN_CEIL_range as [[CR1 CR2] _].
  (* the cells and windows of the post are off Up *)
  assert (OFFT : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> off_ush Up a)
    by (intros a Ha; exact (thread_off_ush im_segs B ly S Up W mem0 md0 a HARU Ha)).
  assert (OFFQ : forall a, ly_Q ly <= a < ly_Q ly + kPtrArrayResv -> off_ush Up a)
    by (intros a Ha; exact (owned_ext_off_ush im_segs B ly S Up W mem0 md0 (ly_Q ly, kPtrArrayResv) a HARU
          ltac:(unfold owned_extents; cbn [In]; tauto) Ha)).
  assert (OFFZ : forall a, ims_dzone ly a -> off_ush Up a).
  { intros a Ha. destruct (ZON ly S W (FSP.unpoison Up mem0) md0 a HAR (or_introl Ha)) as [HR HF].
    exact (ush_free_off im_segs B ly S Up W mem0 md0 a HARU HR HF). }
  assert (OFFS : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> off_ush Up a)
    by (intros a Ha; exact (stack_off_ush im_segs B ly S Up W mem0 md0 a HARU Ha)).
  assert (OFFM : forall a, mb <= a < mb + ImgBaseAGS.MSv n -> off_ush Up a).
  { intros a Ha. apply (band_off im_segs B ly S Up W mem0 md0 a HARU); [lia|].
    unfold kLowShadowBeg, SHADOW_OFF in *. lia. }
  assert (OFFMS : forall a, ImgBaseAGS.SMv mb <= a < ImgBaseAGS.SMv mb + ImgBaseAGS.MSv n / 8 -> off_ush Up a).
  { intros a Ha. unfold ImgBaseAGS.SMv, ImgBaseAGS.SHBv in Ha. rewrite SHB in Ha.
    apply (grant_shadow_off im_segs B ly S Up W mem0 md0 mb (ImgBaseAGS.MSv n) a HARU DJ Ha).
    pose proof (Z.div_mod mb 8 ltac:(lia)). pose proof (Z.mod_pos_bound mb 8 ltac:(lia)).
    pose proof (Z.div_mod (ImgBaseAGS.MSv n) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (ImgBaseAGS.MSv n) 8 ltac:(lia)).
    unfold SHADOW_OFF in *. lia. }
  assert (WOFF : forall a, ImgBaseAGS.WIN ly regs0 n (Z.of_nat (length (st_sec_arr S))) mb a \/
    (grow = true /\ QRz ly (st_sec_reserved S) a) \/ DXz ly (bv_unsigned (getr regs0 2)) a -> off_ush Up a).
  { intros a [HW | [[_ HQ] | HD]].
    - unfold ImgBaseAGS.WIN in HW. cbv zeta in HW. destruct HW as [HW | [HW | [HW | HW]]].
      + apply OFFS. unfold ImgBaseAGS.AFSTACK in *. lia.
      + exact (OFFT a (WINT_thread ly a HW)).
      + apply (OFFI ly S W mem0 md0 a HARU). exact (WINI_inst regs0 n I a (I11 regs0 H11) ltac:(lia) HW).
      + unfold ImgBaseAGS.WINM in HW. cbv zeta in HW. destruct HW as [HW | [HW | HW]].
        * apply OFFQ. unfold ImgBaseAGS.QSv in HW. unfold kMaxNumChunks, kPtrArrayResv in *. lia.
        * exact (OFFM a HW).
        * exact (OFFMS a HW).
    - apply OFFQ. unfold QRz in HQ. lia.
    - unfold DXz in HD. destruct HD as [HD | HD]; [apply OFFS; unfold DEP_STK, ImgBaseAGS.AFSTACK in *; lia | exact (OFFZ a HD)]. }
  (* the AR field at the unpoisoned memories *)
  assert (HSF' : sfin W ly regs0 (FSP.unpoison Up mem0) I n tr (Z.of_nat (length (st_sec_arr S))) (st_sec_reserved S) mb
    (fun zz m => dpost I ly S W tr zz m) grow z Wz regs' (FSP.unpoison Up mem')).
  { refine (sfin_U W ly regs0 mem0 I n tr _ _ mb _ grow z Wz regs' mem' Up ltac:(lia) OFFZ OFFT
      (fun a => OFFI ly S W mem0 md0 a HARU) _ OFFM OFFMS HSF).
    intros a Ha. apply OFFQ. unfold ImgBaseAGS.QSv in Ha. unfold kMaxNumChunks, kPtrArrayResv in *. lia. }
  destruct (Fpost I ly S W (FSP.unpoison Up mem0) md0 n tr regs0 mb grow z Wz mdz regs' (FSP.unpoison Up mem')
    (conj eq_refl HAR) Hr Hn Hl HU (HWFU Up) H11 HGROW HSK HSF' HAOK) as (HARp & HLp & HLE & HUv & FRa & FRr).
  split; [|split; [exact HLp|split; [exact HLE|split; [exact HUv|split]]]].
  + split; [reflexivity|].
    apply (ARU_rebuild im_segs B ly S Up W mem0 md0 (lyFz ly S mb) (SFSz S n tr z grow) Wz mem' mdz HARU (proj2 HARp)).
    * intros r p m _ Hb _ _. exact (blocks_keep B ly S _ mb n tr z grow p m M Hb).
    * intros s Hs. pose proof (ush_band im_segs B ly S Up W mem0 md0 s HARU Hs) as (B1 & B2 & B3).
      assert (RAW : mem' (Z_to_bv 64 s) = mem0 (Z_to_bv 64 s)).
      { pose proof HSF as [_ MEQF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
        apply (MEQF (Z_to_bv 64 s)); rewrite (wz64 s B3); intros HX.
        - exact (off_contra Up s (WOFF s (or_introl HX)) Hs B3).
        - exact (off_contra Up s (WOFF s (or_intror (or_introl HX))) Hs B3).
        - exact (off_contra Up s (WOFF s (or_intror (or_intror HX))) Hs B3). }
      assert (VW : w_H W (Z_to_bv 64 s) = false).
      { destruct (w_H W (Z_to_bv 64 s)) eqn:EH; [|reflexivity]. exfalso.
        pose proof (FSP.ARU_poisoned _ _ _ _ _ _ _ _ HARU s Hs) as P.
        pose proof (proj1 (proj2 (Fledger I ly S W (FSP.unpoison Up mem0) md0 (conj eq_refl HAR)))) as SEGS.
        assert (R0 : seg_rom im_segs (Z_to_bv 64 s) = None)
          by exact (seg_rom_none_above im_segs s SEGS ltac:(unfold kImgEnd, SHADOW_OFF in *; lia)).
        unfold aview, mbyte, mrestrict in P. rewrite EH, R0 in P. cbn in P. discriminate P. }
      unfold aview, mbyte, mrestrict. rewrite VW, (SKmon _ VW), RAW. reflexivity.
  + intros a Ha NA NA' NS NU.
    rewrite <- (aview_unpoison_off im_segs (w_H Wz) Up mem' a (noown_off im_segs B ly S Up W mem0 md0 a HARU Ha NA)).
    rewrite <- (aview_unpoison_off im_segs (w_H W) Up mem0 a (noown_off im_segs B ly S Up W mem0 md0 a HARU Ha NA)).
    exact (FRa a Ha NA NA' NS NU).
  + intros x NA NA' NS NU. pose proof (noown_off_w im_segs B ly S Up W mem0 md0 x HARU NA) as OX.
    rewrite <- (FSP.unpoison_out Up mem' x OX), <- (FSP.unpoison_out Up mem0 x OX). exact (FRr x NA NA' NS NU).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 6. The secondary walk's zones by shape (the premise [zones_free .. ims_dzone (CZS ly I)] of [ifaceS_U]).            *)
(* ---------------------------------------------------------------------------------------------------------------- *)

(* E is a lower bound of the image's end that AR gives (fs: the ledger fact FSupoisonARX.fs_img_end); the depot zone
   is free by its own fact (fs: FSupoisonARX.fs_zones_free); the image cells of CZS lie in [0, SHADOW_OFF), its shadow
   window [ims_shb, ims_csh_end) below the shadow of E, and its thread, context and D cells in owned extents. *)
Lemma zones_free_CZS : forall B (E I : Z),
  (forall ly S W mem md, AR im_segs B ly S W mem md -> E <= fst (ly_img ly) + snd (ly_img ly)) ->
  (forall ly S W mem md a, AR im_segs B ly S W mem md -> ims_dzone ly a -> 0 <= a < 2 ^ 64 /\ ush_free ly a) ->
  0 <= I -> I + 0xe60 <= SHADOW_OFF -> ims_img_end <= SHADOW_OFF ->
  0 <= ims_shb -> ims_csh_end <= shadow_addr E -> 0 <= im_tsd -> im_tsd + 8 <= SHADOW_OFF ->
  zones_free im_segs B ims_dzone (fun ly a => CZS ly I a).
Proof.
intros B E I IMG DZ HI0 HI1 HIE HS0 HS1 HT0 HT1 ly S W mem md a HAR [HD | HC].
- exact (DZ ly S W mem md a HAR HD).
- pose proof (am_layout B ly S _ (proj1 HAR)) as LO.
  pose proof (IMG ly S W mem md HAR) as IE.
  pose proof (lo_img ly LO) as (I0 & I1 & I2 & I3).
  assert (DIV0 : 0 <= (fst (ly_img ly) + snd (ly_img ly)) / 8) by (apply Z.div_pos; unfold kImgLo in *; lia).
  assert (DD : (fst (ly_img ly) + snd (ly_img ly)) / 8 <= kImgEnd / 8)
    by (apply Z.div_le_mono; unfold kImgLo, kImgEnd in *; lia).
  assert (EE : kImgEnd / 8 = 847360) by reflexivity.
  assert (LOWF : forall x, 0 <= x < SHADOW_OFF -> 0 <= x < 2 ^ 64 /\ ush_free ly x).
  { intros x Hx. unfold ush_free, shadow_addr, SHADOW_OFF in *. split; [lia | left; lia]. }
  assert (OWN : forall lo len, In (lo, len) (owned_extents ly) -> lo <= a < lo + len -> 0 <= a < 2 ^ 64 /\ ush_free ly a).
  { intros lo len Hin Ha. pose proof (proj1 (Forall_forall _ _) (lo_app ly LO) (lo, len) Hin) as [P1 P2].
    cbn [fst snd] in P1, P2. pose proof ASAN_CEIL_range as [CR _].
    unfold ush_free, shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
    destruct P2 as [P2|[P2 P3]]; [split; [lia | left; lia] | split; [lia | right; lia]]. }
  unfold CZS in HC.
  destruct HC as [HC | [HC | [HC | [HC | [HC | HC]]]]].
  + apply LOWF. unfold o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, o_comb_stats in HC.
    destruct HC as [HC | [HC | [HC | [HC | [HC | HC]]]]]; lia.
  + pose proof (shadow_addr_mono E _ IE) as SM. unfold ush_free. unfold shadow_addr, SHADOW_OFF in *. split; [lia | left; lia].
  + apply (OWN (ly_T ly) kThreadObjSize); [unfold owned_extents; cbn [In]; tauto | unfold kThreadObjSize; lia].
  + apply (OWN (ly_C ly) 256); [unfold owned_extents; cbn [In]; tauto | lia].
  + apply LOWF. lia.
  + apply (OWN (ly_D ly) 4096); [unfold owned_extents; cbn [In]; tauto | exact HC].
Qed.

End s.
