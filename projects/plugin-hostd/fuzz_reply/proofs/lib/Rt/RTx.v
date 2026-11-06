(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the runtime contracts' laws over a GENERIC allocator relation (fuzz_reply.runtime_twins,
   placed by a Theorem Labs lane 2026-10-29T20:31Z). Image-free: no address, no image class, both images use it.
   - rt_laws segs B ARx: the FIVE facts the proved runtime contracts of fuzz_reply (lib/A/RT_*.v, lib/A/Rt/*.v,
     lib/B/Rt/*.v) read from cgif's AR, stated over ARx (its third argument the head set Hp, as in FCiface.v):
       rtl_frame  = FCiface.AR_frame_law_x  (cgif's al_frame,  YG0d.v:451-458; cf alc_frame),
       rtl_stack  = FCiface.AR_stack_law_x  (cgif's al_stack,  YG0d.v:480-482; cf alc_stack),
       rtl_const  = YCbqG.ARx_const_law's text (cgif's al_const, YG0d.v:473-479; cf alc_const),
       rtl_layout : ARx -> layout_ok ly      (cgif's ARm am_layout, YG0n.v:209; cf ARmcf amc_layout, YG0ncf.v:217),
       rtl_const_cells : the image's const cells hold (= YCbqG.ARx_const_cells_law's text = FCiface.fi_const's;
                         cgif's ARm am_const, YG0n.v:211; cf ARmcf amc_const, YG0ncf.v:219).
     Measured on a working branch afcf21c8a42: the contracts read al_frame / al_stack / al_const
     through the laws,
     layout_ok through `am_layout .. (proj1 HAR)`, and the const cells through `rodata_ok .. (proj1 HAR)` (AE2y.v:197,
     am_const; the memchr / strnlen walks' rodata cells); nothing else of AR. rtl_layout is not a field of
     YCbqG.AR_laws_x, so rt_laws_of_x takes it beside AR_laws_x. QMm W0' (a Theorem Labs lane, 2026-10-30): YCbqG's frame law
     takes the kept-bytes premise, which rtl_frame (FCiface's text) does not, so rt_laws_of_x takes rtl_frame too.
   - Instances: rt_laws_AR (ARx := FCiface.AR_nohp, cgif's AR with Hp ignored; convertible with W_journal_x.ARi),
     rt_laws_AR0 (ARx := AR /\ Hp = [], the same definition as the A side's W_journal_x.ARi0), rt_laws_cf
     (ARx := YG0ncf.ARcf, from
     AR_laws_cf), rt_laws_of_x (from AR_laws_x and the layout fact).
   - The twins of the two shared runtime texts the contracts conclude, over FCiface.ecall_pre_x, with the ghost set
     Hp after S and unchanged through the call (the convention of YG0d2cf.v / FCiface.v / W_sites_x.v):
     Rt/MemchrDef.v's amemchr_realizes / amemchr_realizesM -> amemchr_realizes_x / amemchr_realizesM_x (the latter's
     text is W_drain_cx_x.v:81's, which sits in an A-only file; it is stated here so lib/B's runtime walks can conclude
     it, and the two are convertible), Rt/StrnlenDef.v's astrnlen_whole_realizes / astrnlen_whole_realizesM -> _x.
     Each has its AR bridge (_x_AR: the _x text at AR_nohp gives the AR text). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef StrnlenDef.
Import ListNotations.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- 1. The laws. ---- *)
Section l.
Variable segs : list Segment.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Record rt_laws : Prop := {
rtl_frame : AR_frame_law_x segs B ARx;
rtl_stack : AR_stack_law_x segs B ARx;
rtl_const : forall ly S Hp W mem md,
ARx ly S Hp W mem md ->
rdword (aview segs (w_H W) mem) (as_shadow_cell B) = Some SHADOW_OFF /\
rd32 (aview segs (w_H W) mem) (as_uar_cell B) 1 /\
rdword (aview segs (w_H W) mem) (as_got_shadow B) = Some (as_shadow_cell B) /\
rdword (aview segs (w_H W) mem) (as_got_uar B) = Some (as_uar_cell B);
rtl_layout : forall ly S Hp W mem md, ARx ly S Hp W mem md -> layout_ok ly;
rtl_const_cells : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
Forall (cell_holds B ly (aview segs (w_H W) mem)) (as_const B ly)
}.
Lemma rt_laws_of_x : forall hl, YCbqG.AR_laws_x segs B ARx hl -> AR_frame_law_x segs B ARx ->
(forall ly S Hp W mem md, ARx ly S Hp W mem md -> layout_ok ly) -> rt_laws.
Proof.
intros hl LX LF LY. constructor.
- exact LF.
- exact (YCbqG.alx_stack _ _ _ LX).
- exact (YCbqG.alx_const _ _ _ LX).
- exact LY.
- exact (YCbqG.alx_const_cells _ _ _ LX).
Qed.
End l.

(* ---- 2. The instances. ---- *)
Section i.
Variable segs : list Segment.
Variable B : asyms.
Definition AR_hp0 (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (mem : word -> option byte) (md : Model)
: Prop := AR segs B ly S W mem md /\ Hp = [].
Lemma rt_laws_AR : AR_laws segs B -> rt_laws segs B (AR_nohp segs B).
Proof.
intros LAWS. constructor; unfold AR_nohp.
- intros ly S Hp W mem md mem' md'. exact (al_frame _ _ LAWS ly S W mem md mem' md').
- intros ly S Hp W mem md a. exact (al_stack _ _ LAWS ly S W mem md a).
- intros ly S Hp W mem md. exact (al_const _ _ LAWS ly S W mem md).
- intros ly S Hp W mem md HAR. exact (am_layout _ _ _ _ (proj1 HAR)).
- intros ly S Hp W mem md HAR. exact (am_const _ _ _ _ (proj1 HAR)).
Qed.
Lemma rt_laws_AR0 : AR_laws segs B -> rt_laws segs B AR_hp0.
Proof.
intros LAWS. constructor; unfold AR_hp0.
- intros ly S Hp W mem md mem' md' (HAR & E) H1 H2 H3 H4 H5 H6. split; [|exact E].
  exact (al_frame _ _ LAWS ly S W mem md mem' md' HAR H1 H2 H3 H4 H5 H6).
- intros ly S Hp W mem md a (HAR & _). exact (al_stack _ _ LAWS ly S W mem md a HAR).
- intros ly S Hp W mem md (HAR & _). exact (al_const _ _ LAWS ly S W mem md HAR).
- intros ly S Hp W mem md (HAR & _). exact (am_layout _ _ _ _ (proj1 HAR)).
- intros ly S Hp W mem md (HAR & _). exact (am_const _ _ _ _ (proj1 HAR)).
Qed.
End i.

Section c. Context {ci : CfImg} {cp : CfParams}.
Variable segs : list Segment.
Variable B : asyms.
Lemma rt_laws_cf : AR_laws_cf segs B -> rt_laws segs B (ARcf segs B).
Proof.
intros LAWS. constructor.
- exact (alc_frame _ _ LAWS).
- exact (alc_stack _ _ LAWS).
- exact (alc_const _ _ LAWS).
- intros ly S Hp W mem md HAR. exact (amc_layout _ _ _ _ _ (proj1 HAR)).
- intros ly S Hp W mem md HAR. exact (amc_const _ _ _ _ _ (proj1 HAR)).
Qed.
End c.

(* ---- 3. The twins of the shared runtime texts. ---- *)
Section t.
Variable segs : list Segment.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
(* Rt/MemchrDef.v:23 amemchr_realizes *)
Definition amemchr_realizes_x (pc : Z) : Prop :=
forall ly S Hp W regs mem md x c n,
ecall_pre_x segs B ARx ly S Hp W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 c -> getr regs 12 = w64 n ->
0 <= c < 256 -> 0 <= n < 2 ^ 32 -> 0 < x -> x + n <= 2 ^ 63 ->
src_ok segs W regs mem x n -> amem_range x n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x n ->
(0 < n -> shadow_hull_vis (aview segs (w_H W) mem) x n) ->
rom_view segs W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(exists k, first_byte segs W mem x n c k /\ getr regs' 10 = (if k <? n then w64 (x + k) else w64 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
(* Rt/MemchrDef.v:39 amemchr_realizesM (= W_drain_cx_x.v:81 amemchr_realizesM_x, verbatim) *)
Definition amemchr_realizesM_x (lo hi pc : Z) : Prop :=
forall ly S Hp W regs mem md x c n,
ecall_pre_x segs B ARx ly S Hp W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 c -> getr regs 12 = w64 n ->
0 <= c < 256 -> 0 <= n < 2 ^ 32 -> 0 < x -> x + n <= 2 ^ 63 ->
src_ok segs W regs mem x n -> amem_range x n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x n ->
(0 < n -> shadow_hull_vis (aview segs (w_H W) mem) x n) ->
consts_view segs lo hi W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(exists k, first_byte segs W mem x n c k /\ getr regs' 10 = (if k <? n then w64 (x + k) else w64 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
(* Rt/StrnlenDef.v:22 astrnlen_whole_realizes *)
Definition astrnlen_whole_realizes_x (pc : Z) : Prop :=
forall ly S Hp W regs mem md x n,
ecall_pre_x segs B ARx ly S Hp W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 n -> 0 <= n < 2 ^ 32 -> 0 < x -> x + n <= 2 ^ 63 ->
src_ok segs W regs mem x n -> (forall a, x <= a < x + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) -> amem_range x n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x n ->
(0 < n -> shadow_hull_vis (aview segs (w_H W) mem) x n) ->
rom_view segs W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(exists k, first_byte segs W mem x n 0 k /\ getr regs' 10 = w64 k) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
(* Rt/StrnlenDef.v:38 astrnlen_whole_realizesM *)
Definition astrnlen_whole_realizesM_x (lo hi pc : Z) : Prop :=
forall ly S Hp W regs mem md x n,
ecall_pre_x segs B ARx ly S Hp W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 n -> 0 <= n < 2 ^ 32 -> 0 < x -> x + n <= 2 ^ 63 ->
src_ok segs W regs mem x n -> (forall a, x <= a < x + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) -> amem_range x n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x n ->
(0 < n -> shadow_hull_vis (aview segs (w_H W) mem) x n) ->
consts_view segs lo hi W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(exists k, first_byte segs W mem x n 0 k /\ getr regs' 10 = w64 k) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
End t.

(* ---- 4. The AR bridges: each _x text at AR_nohp (Hp := []) gives the AR text. ---- *)
Section br.
Variable segs : list Segment.
Variable B : asyms.
Lemma amemchr_realizes_x_AR : forall pc, amemchr_realizes_x segs B (AR_nohp segs B) pc -> amemchr_realizes segs B pc.
Proof. intros pc H ly S W regs mem md x c n HPRE. exact (H ly S [] W regs mem md x c n HPRE). Qed.
Lemma amemchr_realizesM_x_AR : forall lo hi pc,
amemchr_realizesM_x segs B (AR_nohp segs B) lo hi pc -> amemchr_realizesM segs B lo hi pc.
Proof. intros lo hi pc H ly S W regs mem md x c n HPRE. exact (H ly S [] W regs mem md x c n HPRE). Qed.
Lemma astrnlen_whole_realizes_x_AR : forall pc,
astrnlen_whole_realizes_x segs B (AR_nohp segs B) pc -> astrnlen_whole_realizes segs B pc.
Proof. intros pc H ly S W regs mem md x n HPRE. exact (H ly S [] W regs mem md x n HPRE). Qed.
Lemma astrnlen_whole_realizesM_x_AR : forall lo hi pc,
astrnlen_whole_realizesM_x segs B (AR_nohp segs B) lo hi pc -> astrnlen_whole_realizesM segs B lo hi pc.
Proof. intros lo hi pc H ly S W regs mem md x n HPRE. exact (H ly S [] W regs mem md x n HPRE). Qed.
End br.
End a.
