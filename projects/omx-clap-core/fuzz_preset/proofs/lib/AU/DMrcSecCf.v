(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/DMrcSecCf.v (commit ce1a656b52b7, file sha256 b0db9ca68c79) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its image-row names to preset's (ReplyImg_* -> PresetImg_*, *reply -> *preset); its 1 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 8 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMrcSecCf.v (commit 3d8ad2aeb77e, H4 cf instance set (reply-rccf); file sha256 032d151bfde9) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMrcSecCf.v at commit 2c35faeeaec, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (3 numerals; per-numeral report). *)
(* Theorem Labs, 2026-10-30 (lane B1, slice H4): H4's secondary step field DMrcSecReads.rc_sec_step_g at cgif's image
   over the loosened post relation, and its flag-free form DMrcSecNf.rc_sec_step_nf_g, from the cf layer's secondary
   step with its budget loosened, YGcfInstRcSec.rc_sec_step_sl_cf (F1 row R3, re-hide twin).
   rule 24: no function proved (kind: field discharge).

   WHAT.  [ARXsl_cf B IOK Hp d]: the cf cut relation YGcfInstDrainR.ARXr_cf B IOK Hp with its budget loosened by d
   bytes: the instance predicate, YGcfRehideAR.ARcfR_sl at d and xs_mapped_cf (ARXr_cf's shape, ARcfR_sl for ARcfR).
   [REC_LE]: the unit's per-recycle hull charge cf_rec_drop LEN is at most the re-hidden interior
   YGcfRehidePost.rh_hi MAP LEN - YGcfRehidePost.rh_lo MAP of a map at MAP >= 0 with kMaxSize + kPage <= LEN.
   cf_rec_drop is a CfParams field, so at the generic instance this bound is a named premise; each unit proves it
   from its law (YGcfRehideAR.reply_rec_drop_le_rh, preset_rec_drop_le_rh: these premises are exactly what the two
   laws take).
   [rc_sec_step_nf_sl_of_cf]: for every B with TfibSyms B and every IOK, Hp, the row ERRB_QAPART and REC_LE give the
   flag-free field DMrcSecNf.rc_sec_step_nf_g B at pre relation ARXr_cf B IOK Hp, post relation ARXsl_cf B IOK Hp and
   AOX := aowned B (the owned set the cf instance gives H4's fields, YGcfInstRcPrim.v:12): the post holds at the
   recycled slot's slack rh_hi MAP LEN - rh_lo MAP.  [rc_sec_step_sl_of_cf]: the same at DMrcSecReads.rc_sec_step_g
   (rcc_pre_x), through DMiface.rcc_pre_sec_of_x, its post's flag the pre's (X2v keeps st_cache_inited by computation).

   HOW.  rc_sec_step_sl_cf gives ARcfR_sl at slack cf_rec_drop (sm_len sm); YGcfRehideAR.ARcfR_sl_mono with REC_LE at
   MAP = YFg8.MAP ly r (4096 <= MAP, [GEO]) and LEN = YFg8.LEN sm (kMaxSize + kPage <= LEN, [LEN_M2]: the chunk's
   chunk_ok_cf through YGcfRehideAR.M2_of_pre) loosens it to the slot's slack.  rc_sec_step_sl_cf's premises, from
   the field's:
   - the image premises at AGif2cgif.AImg_cgif: im_syms B is TfibSyms B; IMG_SAPART by TfibSyms' numerals; IMG_JUNK
     by ts_junk (the junk lies in [0xa2000, 0x601000)) and the last two segments of tfibsegs, which tile that interval;
   - the memory premises from the walk's frame (DMrcSecMun.LINKD, DMrcSecGv.at_RET): off WPRE / WIN3 the memory is the
     call's, and WPRE / WIN3 lie in the cf window rsD ([win_rsD]: the stack part, the allocator words, the thread
     stats, the slot, the last entry's index word, or the dead map itself when the dead entry is the last one, the
     map's shadow and the map); the written words, presence and the shadow's zero fill are at_RET's;
   - the model premises: with_vm_backing keeps the maps and the lazy list, so the unmap of the backed model has the
     maps, lazy list and eager use of the unmap of the model;
   - the state equalities [X2_eq] (rsX2 = YFg8.X2v) and [W2_eq] (W2 = YFg8.W2, by LEN k = sm_len sm of the cut
     relation's chunk facts).
   The conclusion's window: rsDS (YFeu.KSTACK = 512 below the entry sp) is in ascratch at KSTACK_CF = 2048.  The puser
   step holds by computation: the step changes the chunks, the secmaps and the pointer array only. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YFg8.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YFfn YK0v YK0g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YFf3 YFeu. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require DMrcSecGv DMrcSecMun DMrcSecF6 DMrcSecReads DMrcSecNf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG03cf YGcfXs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstDrainR. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require YGcfInstRcSec. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost YGcfRehideAR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.

From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfImgRows.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : YGcfNames.CfImg} {cp : CfParams}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The image premises of rc_sec_step_sl_cf at cgif's image.                                                         *)
Lemma im_syms_preset : forall B, TfibSyms B -> @im_syms AImg_cgif B.
Proof. intros B TB. exact TB. Qed.

Lemma img_sapart_preset : @YGcfInstRcSec.IMG_SAPART AImg_cgif.
Proof.
intros B TB a Hs. change (TfibSyms B) in TB. unfold YGcfInstRcSec.sdeal_inst in Hs.
rewrite (ts_inst _ TB) in Hs. rewrite (ts_depot _ TB), (ts_store _ TB), (ts_ial_lo _ TB), (ts_ial_hi _ TB), (ts_ial_flag _ TB).
unfold TFIB_INST, TFIB_DEPOT, TFIB_STORE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in *. lia.
Qed.

(* The junk lies in [0xa2000, 0x601000) (ts_junk), which the segments [0xa2000, 0xa4000) and [0xa4000, 0x601000) of
   tfibsegs tile. *)
Lemma img_junk_preset : @YGcfInstRcSec.IMG_JUNK rc AImg_cgif.
Proof.
intros B ly r0 TB _ Hr j Hj. change (TfibSyms B) in TB.
destruct (ts_junk _ TB ly r0 Hr) as (z & Ez & Z1 & Z2). rewrite Ez. cbn [aeval].
destruct (Z_lt_le_dec (z + j) 671744) as [L|L].
- exists AsanUbsan.AsanUbsan_segment_002. split; [do 2 right; left; reflexivity | cbn; lia].
- exists AsanUbsan.AsanUbsan_segment_003. split; [do 3 right; left; reflexivity | cbn; lia].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The loosened cut relation, and the unit's recycle charge within the re-hidden interior.                          *)
(* YGcfInstDrainR.ARXr_cf B IOK Hp with ARcfR_sl at d for ARcfR (the cf cut relation, its budget loosened by d). *)
Definition ARXsl_cf (B : asyms) (IOK : Z -> Prop) (Hp : list Z) (d : Z) :
  Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop :=
fun inst ly S W mem md => IOK inst /\ YGcfRehideAR.ARcfR_sl tfibsegs B ly S Hp W mem md d /\ YGcfXs.xs_mapped_cf ly S md.
(* cf_rec_drop is a CfParams field: at the generic instance its bound by the re-hidden interior is this named premise
   (each unit: YGcfRehideAR.reply_rec_drop_le_rh / preset_rec_drop_le_rh). *)
Definition REC_LE : Prop :=
forall MAP LEN, 0 <= MAP -> kMaxSize + kPage <= LEN -> cf_rec_drop LEN <= YGcfRehidePost.rh_hi MAP LEN - YGcfRehidePost.rh_lo MAP.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The model: with_vm_backing keeps the maps and the lazy list, so the unmap after it is the unmap's.              *)
Lemma munmap_wvb_maps : forall a n mat1 md,
m_vmmaps (YK0v.munmap_model a n (with_vm_backing (m_vm_lazy md) mat1 md)) = m_vmmaps (YK0v.munmap_model a n md).
Proof. intros a n mat1 md. destruct md as [fd0 [maps0 lz0 mt0] io0 fs0 proc0 lim0 tm0]. reflexivity. Qed.
Lemma munmap_wvb_lazy : forall a n mat1 md,
m_vm_lazy (YK0v.munmap_model a n (with_vm_backing (m_vm_lazy md) mat1 md)) = m_vm_lazy (YK0v.munmap_model a n md).
Proof. intros a n mat1 md. destruct md as [fd0 [maps0 lz0 mt0] io0 fs0 proc0 lim0 tm0]. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The field's premises, as Section hypotheses in the field's order.                                               *)
Section f.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variable IOK : Z -> Prop.
Variable Hp : list Z.
(* The cf image rows rc_sec_step_sl_cf takes (P'' YGcfImgRows / YGcfInstBase; properties of the cf instance's CfImg). *)
Hypothesis EAP : YGcfImgRows.ERRB_QAPART.
(* the unit's recycle charge within the re-hidden interior *)
Hypothesis RLE : REC_LE.
Variables (inst : Z) (ly : alayout) (X : astate) (k : chunk) (cbp : Z) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (r : nat) (o : Z) (sm : secmap) (i : nat) (regsD : bvmap 5 word)
  (memD : word -> option byte) (mat1 : list word) (regs' : bvmap 5 word) (mem' : word -> option byte) (mat : list word).
Local Notation ARXr := (@YGcfInstDrainR.ARXr_cf rc ci cp AImg_cgif B IOK Hp).
Local Notation MAP := (YFg8.MAP ly r).
Local Notation LEN := (YFg8.LEN sm).
Local Notation QI := (YFg8.qi ly i).
Local Notation LST := (YFg8.lst ly X r).
Local Notation mdM := (YK0v.munmap_model (w64 MAP) (w64 LEN) (with_vm_backing (m_vm_lazy md) mat1 md)).
Hypothesis PRE : @rcc_pre_sec AImg_cgif B ARXr inst ly X k cbp W regs mem md.
Hypothesis Hb : ck_beg k = PSec r o.
Hypothesis Hsm : nth_error (st_secs X) r = Some sm.
Hypothesis Hi : nth_error (st_sec_arr X) i = Some r.
Hypothesis Hk : In k (st_chunks X).
Hypothesis Hst : ck_state k = CQuarantined.
Hypothesis Hni : ~ In (ck_beg k) (map ck_beg (q_items X)).
Hypothesis LNK : DMrcSecMun.LINKD ly W regs mem regsD memD.
Hypothesis HR : DMrcSecGv.at_RET W ly regsD memD MAP LEN (YFg8.idx i) (YFg8.nA X) QI LST
  (DMrcSecF6.v regs 1%bv) (DMrcSecF6.v regs 8%bv) (DMrcSecF6.v regs 9%bv) (DMrcSecF6.v regs 18%bv) (YFg8.own X i) mdM
  W (mkCfg (mkst regs' (w64 (DMrcSecF6.v regs 1%bv)) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy mdM) mat mdM)).
Hypothesis CONST' : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem')) (as_const B ly).

Lemma AR : ARXr inst ly X W mem md. Proof. exact (proj1 PRE). Qed.
Lemma MR : @YGcfInstDrainR.ARcfR rc ci cp tfibsegs B ly X Hp W mem md. Proof. exact (proj1 (proj2 AR)). Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The state equalities.                                                                                            *)
Lemma LEN_eq : YGcfInstRcSec.LEN k = LEN.
Proof.
destruct (@YGcfInstRcSec.KFACTS rc ci cp AImg_cgif B ly X Hp k r o sm W mem md MR Hk Hb Hsm) as (_ & E & _).
unfold YFg8.LEN. symmetry. exact E.
Qed.
Lemma W2_eq : YGcfInstRcSec.W2 (IM := AImg_cgif) ly k r W = YFg8.W2 ly W r sm.
Proof. unfold YGcfInstRcSec.W2, YFg8.W2, YFg8.iv. rewrite LEN_eq. reflexivity. Qed.
Lemma X2_eq : YGcfInstRcSec.rsX2 X k r sm i = YFg8.X2v X k r sm i.
Proof.
unfold YGcfInstRcSec.rsX2, YGcfInstRcSec.arr', YGcfInstRcSec.arr, YGcfInstRcSec.lastr, YFg8.X2v, YFg8.X2, YFg8.X1, YFf3.X1.
first [reflexivity | destruct X; reflexivity].
Qed.
Lemma OL : YGcfInstRcSec.own X i = true -> LST = ly_sec ly r.
Proof.
intros Eo. pose proof (@YGcfInstRcSec.ARR rc ci cp AImg_cgif B ly X Hp r i W mem md MR Hi) as (_ & _ & _ & _ & _ & _ & _ & OWN).
pose proof (proj1 OWN Eo) as E0. unfold YGcfInstRcSec.lastr, YGcfInstRcSec.arr in E0. unfold YFg8.lst. rewrite E0. reflexivity.
Qed.
Lemma GEO : 8192 <= LEN /\ 4096 <= MAP /\ MAP + LEN <= ASAN_CEIL.
Proof.
pose proof (@YGcfInstRcSec.geom rc ci cp AImg_cgif B ly X Hp k r o sm W mem md MR Hk Hb Hsm) as (_ & G2 & _ & _ & G5 & G6).
rewrite LEN_eq in G2, G5. unfold YGcfInstRcSec.MAP in G5, G6. unfold YFg8.MAP. lia.
Qed.
(* The map is at least kMaxSize + kPage: the chunk's chunk_ok_cf (the cut relation's WfR_cf) and secondary_geometry. *)
Lemma LEN_M2 : kMaxSize + kPage <= LEN.
Proof.
exact (YGcfRehideAR.M2_of_pre X k r o sm
  (proj1 (Forall_forall _ _) (YG03cf.wfr_chunks _ _ _ _ _ (YGcfInstDrainR.amr_wfr _ _ _ _ _ (proj1 MR))) k Hk) Hb Hsm).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The walk's windows lie in the cf window rsD at sp = the entry sp.                                                *)
Lemma win_rsD : forall a, DMrcSecMun.WPRE ly regs a \/ DMrcSecGv.WIN3 ly regs MAP LEN QI LST a ->
YGcfInstRcSec.rsD B ly X k r i (spZ regs) a.
Proof.
intros a Hw. pose proof GEO as (G1 & G2 & G3). pose proof LEN_eq as EL. pose proof (ts_inst _ TB) as EI.
unfold YGcfInstRcSec.rsD, YGcfInstRcSec.rsDS, YGcfInstRcSec.rsDI, YGcfInstRcSec.rsDJ, YGcfInstRcSec.rsDQ,
  YGcfInstRcSec.rsDL, YGcfInstRcSec.rsDH, YGcfInstRcSec.rsDM, shadow_addr, spZ.
rewrite EI, EL.
change (YGcfInstRcSec.MAP ly r) with MAP. change (YGcfInstRcSec.qi ly i) with QI. change (YGcfInstRcSec.lst ly X r) with LST.
unfold DMrcSecMun.WPRE, DMrcSecGv.WIN3, DMrcSecGv.WIN, DMrcSecGv.WINS, DMrcSecGv.WINM, DMrcSecGv.SHAv, DMrcSecGv.CNTv in Hw.
cbv zeta in Hw.
unfold A_ALLOCATOR, TFIB_INST, DMrcSecGv.GDEPTH, YFeu.KSTACK in Hw |- *.
destruct Hw as [[H|[H|H]]|[[H|[H|[H|[H|[H|[H|[H|H]]]]]]]|[H|H]]].
- left. lia.
- right; left. lia.
- do 2 right; left. lia.
- left. lia.
- right; left. lia.
- right; left. lia.
- right; left. lia.
- right; left. lia.
- do 3 right; left. exact H.
- do 2 right; left. lia.
- destruct (YGcfInstRcSec.own X i) eqn:Eo.
  + do 6 right. rewrite (OL Eo) in H. unfold YFg8.MAP in *. lia.
  + do 4 right; left. split; [reflexivity | exact H].
- do 5 right; left. lia.
- do 6 right. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The walk's frame at the return.                                                                                   *)
Lemma LSP : getr regsD 2 = getr regs 2. Proof. exact (proj1 LNK). Qed.
Lemma W3E : forall a, DMrcSecGv.WIN3 ly regsD MAP LEN QI LST a <-> DMrcSecGv.WIN3 ly regs MAP LEN QI LST a.
Proof. intros a. unfold DMrcSecGv.WIN3, DMrcSecGv.WIN. cbv zeta. rewrite LSP. tauto. Qed.
Lemma RETF :
(forall x : word, ~ DMrcSecGv.WIN3 ly regs MAP LEN QI LST (bv_unsigned x) -> mem' x = memD x) /\
(forall x : word, DMrcSecGv.WINS MAP LEN (bv_unsigned x) -> mem' x = Some (Z_to_bv 8 0)) /\
(forall a, bv_unsigned (getr regs 2) - DMrcSecGv.GDEPTH <= a < bv_unsigned (getr regs 2) -> apresent (w_H W) mem' a) /\
(forall a, (QI <= a < QI + 8) \/ (ly_T ly + t_stats + 88 <= a < ly_T ly + t_stats + 104) -> apresent (w_H W) mem' a) /\
val_mem tfibsegs (mrestrict (w_H W) mem') (A_ALLOCATOR + 680) 4 0 /\
val_mem tfibsegs (mrestrict (w_H W) mem') (A_ALLOCATOR + 120) 8 (YFg8.nA X - 1) /\
val_mem tfibsegs (mrestrict (w_H W) mem') (A_ALLOCATOR + 128) 1 0 /\
(exists v, val_mem tfibsegs (mrestrict (w_H W) mem') (A_ALLOCATOR + 144) 8 v) /\
(exists v, val_mem tfibsegs (mrestrict (w_H W) mem') (A_ALLOCATOR + 152) 8 v) /\
(exists v, val_mem tfibsegs (mrestrict (w_H W) mem') (A_ALLOCATOR + 704) 8 v) /\
(exists v, val_mem tfibsegs (mrestrict (w_H W) mem') (A_ALLOCATOR + 712) 8 v) /\
val_mem tfibsegs (mrestrict (w_H W) mem') QI 8 LST /\
(YFg8.own X i = false -> val_mem tfibsegs (mrestrict (w_H W) mem') (LST + 24) 8 (YFg8.idx i) /\
  forall a, LST + 24 <= a < LST + 32 -> apresent (w_H W) mem' a).
Proof.
pose proof HR as (_ & regs0 & mem0 & mat0 & Ec & _ & _ & _ & _ & _ & MEQ & SHD & PS & PQ & VALS).
injection Ec; intros; subst mem0.
unfold DMrcSecGv.MEQP in MEQ. unfold DMrcSecGv.SHD in SHD.
split. { intros x Nx. apply MEQ. rewrite W3E. exact Nx. }
split. { exact SHD. }
split. { intros a Ha. apply PS. rewrite LSP. exact Ha. }
split. { exact PQ. }
cbv zeta in VALS. exact VALS.
Qed.
Lemma KEEP : forall x : word, ~ DMrcSecMun.WPRE ly regs (bv_unsigned x) ->
~ DMrcSecGv.WIN3 ly regs MAP LEN QI LST (bv_unsigned x) -> mem' x = mem x.
Proof. intros x N1 N2. pose proof RETF as (M & _). rewrite (M x N2). exact (proj1 (proj2 (proj2 LNK)) x N1). Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* rc_sec_step_cf_nf's call premises.                                                                               *)
Lemma HSP : ly_stk_lo ly + YFeu.KSTACK <= spZ regs <= ly_stk_hi ly.
Proof. destruct PRE as (_ & _ & _ & _ & H1 & H2 & H3 & _). unfold YFeu.KSTACK, KSTACK_CF in *. lia. Qed.

Lemma AG : forall a, 0 <= a < 2 ^ 64 -> ~ YGcfInstRcSec.rsD B ly X k r i (spZ regs) a ->
aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a.
Proof.
intros a Ha ND. apply aview_same.
apply KEEP; rewrite unsigned_lit_small by exact Ha; intros Hw; apply ND, win_rsD; first [left; exact Hw | right; exact Hw].
Qed.

Lemma EQb : forall a, in_band_rw a -> ~ YGcfInstRcSec.rsD B ly X k r i (spZ regs) a -> mem' (w64 a) = mem (w64 a).
Proof.
intros a Hb0 ND.
assert (Ha : 0 <= a < 2 ^ 64) by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hb0; lia).
unfold w64. apply KEEP; rewrite unsigned_lit_small by exact Ha; intros Hw; apply ND, win_rsD; first [left; exact Hw | right; exact Hw].
Qed.

Lemma ZE : forall a, YGcfInstRcSec.rsDH ly k r a -> mem' (w64 a) = Some (Z_to_bv 8 0).
Proof.
intros a H. pose proof (@YGcfInstRcSec.DH_zone rc ci cp AImg_cgif B ly X Hp k r o sm W mem md MR Hk Hb Hsm a H) as Z0.
assert (Ha : 0 <= a < 2 ^ 64) by (unfold SHADOW_OFF, kHighMemBeg in Z0; lia).
pose proof RETF as (_ & SH & _). unfold w64. apply SH. rewrite unsigned_lit_small by exact Ha.
unfold YGcfInstRcSec.rsDH, shadow_addr in H. rewrite LEN_eq in H. unfold DMrcSecGv.WINS, DMrcSecGv.SHAv, DMrcSecGv.CNTv. exact H.
Qed.

Lemma MUTv : forall j, 0 <= j < 4 -> aview tfibsegs (w_H W) mem' (as_inst B + 680 + j) = Some 0.
Proof.
intros j Hj. pose proof RETF as (_ & _ & _ & _ & V & _).
rewrite (ts_inst _ TB). replace (TFIB_INST + 680 + j) with (A_ALLOCATOR + 680 + Z.of_nat (Z.to_nat j)) by (unfold TFIB_INST, A_ALLOCATOR; lia).
rewrite (YFg8.val_mem_aview _ _ _ 4 0 (Z.to_nat j) V ltac:(lia)). f_equal.
unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity.
Qed.

Lemma NSv : forall kk, (kk < 8)%nat ->
aview tfibsegs (w_H W) mem' (as_inst B + 120 + Z.of_nat kk) = Some (le_byte (YGcfInstRcSec.nA X - 1) 8 kk).
Proof.
intros kk Hkk. pose proof RETF as (_ & _ & _ & _ & _ & V & _).
rewrite (ts_inst _ TB). change TFIB_INST with A_ALLOCATOR. exact (YFg8.val_mem_aview _ _ _ 8 _ kk V Hkk).
Qed.

Lemma QIv : forall kk, (kk < 8)%nat ->
aview tfibsegs (w_H W) mem' (YGcfInstRcSec.qi ly i + Z.of_nat kk) = Some (le_byte (YGcfInstRcSec.lst ly X r) 8 kk).
Proof.
intros kk Hkk. pose proof RETF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V & _).
exact (YFg8.val_mem_aview _ _ _ 8 _ kk V Hkk).
Qed.

Lemma LSTv : YGcfInstRcSec.own X i = false -> forall kk, (kk < 8)%nat ->
aview tfibsegs (w_H W) mem' (YGcfInstRcSec.lst ly X r + 24 + Z.of_nat kk) = Some (le_byte (YGcfInstRcSec.idx i) 8 kk).
Proof.
intros Eo kk Hkk. pose proof RETF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VO).
exact (YFg8.val_mem_aview _ _ _ 8 _ kk (proj1 (VO Eo)) Hkk).
Qed.

(* Presence: off the dead map, a visible byte stays visible. *)
Lemma VISv : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) mem a <> None -> ~ YGcfInstRcSec.rsDM ly k r a ->
aview tfibsegs (w_H W) mem' a <> None.
Proof.
intros a Ha HV NM.
pose proof RETF as (MD & SH & PS & PQ & V680 & V120 & V128 & [v1 V144] & [v2 V152] & [v3 V704] & [v4 V712] & VQI & VOWN).
assert (NM' : ~ (MAP <= a < MAP + LEN)) by (intros HM; apply NM; unfold YGcfInstRcSec.rsDM; rewrite LEN_eq; exact HM).
assert (PV : apresent (w_H W) mem' a -> aview tfibsegs (w_H W) mem' a <> None) by (apply YFg8.apresent_vis; exact Ha).
assert (D : DMrcSecGv.WIN3 ly regs MAP LEN QI LST a \/ ~ DMrcSecGv.WIN3 ly regs MAP LEN QI LST a)
  by (unfold DMrcSecGv.WIN3, DMrcSecGv.WIN, DMrcSecGv.WINS, DMrcSecGv.WINM; cbv zeta; lia).
destruct D as [Hw|Nw].
- unfold DMrcSecGv.WIN3, DMrcSecGv.WIN, DMrcSecGv.WINS, DMrcSecGv.WINM in Hw. cbv zeta in Hw.
  destruct Hw as [[H|[H|[H|[H|[H|[H|[H|H]]]]]]]|[H|H]].
  + apply PV. apply PS. exact H.
  + exact (YFg8.val_mem_vis _ _ _ 4 0 a V680 ltac:(cbn; lia)).
  + destruct (Z_lt_le_dec a (A_ALLOCATOR + 128)) as [L|L].
    * exact (YFg8.val_mem_vis _ _ _ 8 _ a V120 ltac:(cbn; lia)).
    * exact (YFg8.val_mem_vis _ _ _ 1 0 a V128 ltac:(cbn; lia)).
  + destruct (Z_lt_le_dec a (A_ALLOCATOR + 152)) as [L|L].
    * exact (YFg8.val_mem_vis _ _ _ 8 v1 a V144 ltac:(cbn; lia)).
    * exact (YFg8.val_mem_vis _ _ _ 8 v2 a V152 ltac:(cbn; lia)).
  + destruct (Z_lt_le_dec a (A_ALLOCATOR + 712)) as [L|L].
    * exact (YFg8.val_mem_vis _ _ _ 8 v3 a V704 ltac:(cbn; lia)).
    * exact (YFg8.val_mem_vis _ _ _ 8 v4 a V712 ltac:(cbn; lia)).
  + apply PV. apply PQ. left. exact H.
  + apply PV. apply PQ. right. exact H.
  + destruct (YFg8.own X i) eqn:Eo.
    * exfalso. pose proof GEO as (G1 & _). rewrite (OL Eo) in H. unfold YFg8.MAP in NM'. lia.
    * apply PV. exact (proj2 (VOWN eq_refl) a H).
  + destruct (w_H W (Z_to_bv 64 a)) eqn:Hh.
    * exfalso. exact (HV (YFg8.aview_hidden_none W mem a Hh)).
    * apply PV. split; [exact Hh|]. exists (Z_to_bv 8 0). apply SH. rewrite unsigned_lit_small by exact Ha. exact H.
  + exfalso. exact (NM' H).
- assert (E1 : mem' (Z_to_bv 64 a) = memD (Z_to_bv 64 a)) by (apply MD; rewrite unsigned_lit_small by exact Ha; exact Nw).
  assert (DP : DMrcSecMun.WPRE ly regs a \/ ~ DMrcSecMun.WPRE ly regs a) by (unfold DMrcSecMun.WPRE; cbv zeta; lia).
  destruct DP as [HW0|NP].
  + unfold DMrcSecMun.WPRE in HW0. cbv zeta in HW0. destruct HW0 as [H|[H|H]].
    * exfalso. apply Nw. unfold DMrcSecGv.WIN3, DMrcSecGv.WIN. cbv zeta. left. left. exact H.
    * exfalso. apply Nw. unfold DMrcSecGv.WIN3, DMrcSecGv.WIN. cbv zeta. left. right. left. exact H.
    * apply PV. destruct (proj2 (proj2 (proj2 LNK)) a H) as [Hh [b Hb1]]. split; [exact Hh|]. exists b. rewrite E1. exact Hb1.
  + rewrite (aview_same (w_H W) mem mem' a); [exact HV|]. rewrite E1. apply (proj1 (proj2 (proj2 LNK))).
    rewrite unsigned_lit_small by exact Ha. exact NP.
Qed.

Lemma Ev : m_vmmaps (with_vm_backing (m_vm_lazy mdM) mat mdM) =
m_vmmaps (YK0v.munmap_model (w64 (YGcfInstRcSec.MAP ly r)) (w64 (YGcfInstRcSec.LEN k)) md).
Proof. rewrite LEN_eq, YK0g.m_vmmaps_with_vm_backing. apply munmap_wvb_maps. Qed.
Lemma El : m_vm_lazy (with_vm_backing (m_vm_lazy mdM) mat mdM) =
m_vm_lazy (YK0v.munmap_model (w64 (YGcfInstRcSec.MAP ly r)) (w64 (YGcfInstRcSec.LEN k)) md).
Proof. rewrite LEN_eq, YK0g.m_vm_lazy_with_vm_backing. apply munmap_wvb_lazy. Qed.
Lemma Ee : eager_used (with_vm_backing (m_vm_lazy mdM) mat mdM) =
eager_used (YK0v.munmap_model (w64 (YGcfInstRcSec.MAP ly r)) (w64 (YGcfInstRcSec.LEN k)) md).
Proof. unfold eager_used. rewrite Ev, El. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The field's conclusion: the post relation loosened to the recycled slot's slack.                                  *)
Lemma step_sl_cf :
ARXsl_cf B IOK Hp (YGcfRehidePost.rh_hi MAP LEN - YGcfRehidePost.rh_lo MAP) inst ly (YFg8.X2v X k r sm i) (YFg8.W2 ly W r sm)
  mem' (with_vm_backing (m_vm_lazy mdM) mat mdM) /\
(forall a, 0 <= a < 2 ^ 64 -> DMrcSecMun.WPRE ly regs a \/ DMrcSecGv.WIN3 ly regs MAP LEN QI LST a ->
 aowned B ly X a \/ ascratch B KSTACK_CF regs a) /\
(forall a, aowned B ly (YFg8.X2v X k r sm i) a -> aowned B ly X a) /\
(forall a, YFeuC.puser ly X a -> YFeuC.puser ly (YFg8.X2v X k r sm i) a) /\
(forall a, YFeuC.puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) ->
 ~ DMrcSecMun.WPRE ly regs a /\ ~ DMrcSecGv.WIN3 ly regs MAP LEN QI LST a).
Proof.
destruct (@YGcfInstRcSec.rc_sec_step_sl_cf rc ci cp AImg_cgif B IOK Hp EAP inst ly X k r o sm i (spZ regs) W mem md mem'
  (with_vm_backing (m_vm_lazy mdM) mat mdM) AR Hk Hst Hb Hni Hsm Hi HSP (im_syms_preset B TB) img_sapart_preset
  img_junk_preset AG VISv MUTv NSv QIv LSTv CONST' EQb ZE Ev El Ee) as (HI & SL & XS & WOWN & OWN2 & PUN).
split.
{ rewrite <- X2_eq, <- W2_eq. split; [exact HI|]. split; [|exact XS].
  (* the cf step's slack cf_rec_drop (sm_len sm) is within the slot's: REC_LE at MAP >= 4096, LEN >= kMaxSize + kPage *)
  refine (YGcfRehideAR.ARcfR_sl_mono _ B ly _ Hp _ mem' _ (cf_rec_drop (sm_len sm)) _ _ SL).
  pose proof GEO as (_ & G2 & _).
  exact (RLE MAP LEN ltac:(lia) LEN_M2). }
split.
{ intros a Ha Hw. destruct (WOWN a ltac:(lia) (win_rsD a Hw)) as [O|S]; [left; exact O | right].
  unfold ascratch. left. unfold YGcfInstRcSec.rsDS, YFeu.KSTACK in S. unfold KSTACK_CF. lia. }
split. { intros a Ha. apply OWN2. rewrite X2_eq. exact Ha. }
split. { intros a Ha. exact Ha. }
intros a Ha _. pose proof (PUN a Ha) as ND. split; intros Hw; apply ND, win_rsD; [left | right]; exact Hw.
Qed.
End f.

(* H4's secondary step field at cgif's image, over rcc_pre_sec (DMrcSecNf.rc_sec_step_nf_g), its post relation the
   loosened ARXsl_cf, from the cf layer's flag-free secondary step rc_sec_step_sl_cf. *)
Theorem rc_sec_step_nf_sl_of_cf : forall (B : asyms), TfibSyms B -> forall IOK Hp,
  YGcfImgRows.ERRB_QAPART -> REC_LE ->
  DMrcSecNf.rc_sec_step_nf_g B (@YGcfInstDrainR.ARXr_cf rc ci cp AImg_cgif B IOK Hp) (ARXsl_cf B IOK Hp) (aowned B).
Proof.
intros B TB IOK Hp EAP RLE. unfold DMrcSecNf.rc_sec_step_nf_g.
intros inst ly X k cbp W regs mem md r o sm i regsD memD mat1 regs' mem' mat PRE Hb Hsm Hi Hk Hst Hni LNK.
cbv zeta. intros HR CONST'.
exact (step_sl_cf B TB IOK Hp EAP RLE inst ly X k cbp W regs mem md r o sm i regsD memD mat1 regs' mem' mat
  PRE Hb Hsm Hi Hk Hst Hni LNK HR CONST').
Qed.

(* H4's secondary step field at cgif's image (DMrcSecReads.rc_sec_step_g), its post relation the loosened ARXsl_cf. *)
Theorem rc_sec_step_sl_of_cf : forall (B : asyms), TfibSyms B -> forall IOK Hp,
  YGcfImgRows.ERRB_QAPART -> REC_LE ->
  DMrcSecReads.rc_sec_step_g B (@YGcfInstDrainR.ARXr_cf rc ci cp AImg_cgif B IOK Hp) (ARXsl_cf B IOK Hp) (aowned B).
Proof.
intros B TB IOK Hp EAP RLE. unfold DMrcSecReads.rc_sec_step_g.
intros inst ly X k cbp W regs mem md r o sm i regsD memD mat1 regs' mem' mat PRE Hb Hsm Hi Hk Hst Hni LNK.
cbv zeta. intros HR CONST'.
destruct (rc_sec_step_nf_sl_of_cf B TB IOK Hp EAP RLE inst ly X k cbp W regs mem md r o sm i regsD memD mat1 regs'
  mem' mat (rcc_pre_sec_of_x _ _ _ _ _ _ _ _ _ _ _ PRE) Hb Hsm Hi Hk Hst Hni LNK HR CONST') as (AR2 & WOWN & OWN2 & PUS & PUN).
(* The post's flag is the pre's: X2v keeps st_cache_inited. *)
exact (conj AR2 (conj WOWN (conj OWN2 (conj PUS (conj PUN (proj1 (proj2 PRE))))))).
Qed.
End d.
