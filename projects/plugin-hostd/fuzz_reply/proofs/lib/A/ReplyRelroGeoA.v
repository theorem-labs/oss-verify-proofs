(* Theorem Labs, 2026-10-30 (Geo, a subagent of a Theorem Labs lane, for a Theorem Labs lane's cf layer round 3 at plugin-hostd/fuzz_reply).
   rule 24: no function proved (kind: measurement; per-unit image facts about the layout of reply's image A,
   fuzz_reply.asan, pin sha256 42c58610e125, unstripped twin d751b179ea49; no function walk).

   The RELRO range is CfImg_A's [cf_relro_lo, cf_relro_hi) (A/CfImgA.v:81-83, generated from the ELF's PT_GNU_RELRO).
   Read again from both ELFs for this file: PT_GNU_RELRO p_vaddr 0x9d438, p_memsz 0x1bc8, so [0x9d438, 0x9f000), in the
   pin and in its unstripped twin; it is the whole range of the third PT_LOAD; e_type 2 (ET_EXEC).
   Every bound below is a NAME: the CfImg_A fields, the TfibSyms constants of A/AF0m.v (TFIB_ERRNO, TFIB_IAL_LO,
   TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_STORE, TFIB_OOM), DRVW_lo of A/AD1ycf.v, and AD20.RS_LO (see 5). No numeral is
   typed in a term except those of the owners' texts (65536, 8, the 0 of `ew E 0`, and the 0, 2 and 2 ^ 64 of 8's text).

   Eight facts (the eighth, zones_miss_relro_reply_A, is described at the end of the file):
   1. relro_geo_reply_A: no write window of the driver (drv_win_ok, A/AD1ycf.v:52) covers a RELRO byte, when the stack
      pointer is at least 65536 above cf_relro_hi (a Theorem Labs lane's ruling, 14:00Z: the stack premise is REQUIRED; without it
      the stack window [sp - 65536, sp) can reach the range). From in_wrange_drv (A/AD1ycf.v:59) and DRVW_lo
      (A/AD1ycf.v:42, the driver's image windows start at 0xa1f78, above cf_relro_hi = 0x9f000).
   2. relro_seg_reply_A: round 3's relro_seg_t (Reusable/YG0ncf.v:646-647) at tfibsegs: one segment holds the range.
   3. errno_relro_reply_A: round 3's errno_relro_t (Reusable/YG0ncf.v:648) at TfibSyms: errno (TFIB_ERRNO) is above.
   4. pf_ial_apart_reply_A: the layer's pf_ial_apart_t (Reusable/YG0ncf.v:189 on this base, a working branch
      b38406ef4b14) at TfibSyms: Printf's two cells lie outside the internal allocator's arena and its flag.
   5. dzone_static_text_A: the FIRST disjunct of AFgi.DZONE (A/AFgi.v:484-485) is [dzone_static_lo, dzone_static_hi),
      by reflexivity. DZONE writes the two bounds as inline numerals; the names here are other files' names for the
      same addresses: dzone_static_lo := TFIB_STORE (A/AF0m.v:18, __sanitizer::stackStore), dzone_static_hi :=
      AD20.RS_LO (A/AD20.v:46, the start of the driver's global read_stage). Both read from the unstripped twin's
      .symtab for this file: stackStore 0x177f88 (size 0x10010); read_stage 0x5c8710 (size 0x10000), right after
      __ubsan::ubsan_flags, which ends at 0x5c8710.
   6. pf_cells_apart_reply_A: the layer's pf_cells_apart_t (Reusable/YG0ncf.v:203 on this base) at TfibSyms: Printf's
      two cells lie below the stack store, off the out-of-memory byte and outside the error-message-buffer object.
   7. pf_dzone_static_reply_A: the static half of PF_APART (a Theorem Labs lane 15:53Z): Printf's two cells lie outside DZONE's
      first disjunct, from 6 at the image's TfibB (A/AD2l.v:16, TfibB_syms :74). The ly-dependent NB / SB half is not
      here. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YG0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP09 YG0f YGcfNames.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0ncf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AF0m CfImgA AD1ycf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AFgi AD20 AD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AF0x DGbase ImgBaseDG DGgm DGgi DGif0.
Open Scope Z_scope.

(* Image A's CfImg for the texts below, as A/ReplyATopX.v:133 takes it. *)
#[local] Existing Instance CfImg_A.

(* 1. RELRO geometry. *)
Lemma relro_geo_reply_A : forall E rs a, forallb drv_win_ok rs = true -> cf_relro_hi + 65536 <= bv_unsigned (ew E 0) ->
cf_relro_lo <= a < cf_relro_hi -> ~ in_wrange E rs a.
Proof.
intros E rs a Hok Hsp Ha Hw. destruct (AD1ycf.in_wrange_drv E rs a Hok Hw) as [Hs|Hd].
- lia.
- apply AD1ycf.DRVW_lo in Hd. cbn [cf_relro_lo cf_relro_hi CfImg_A] in Ha. lia.
Qed.

(* 2. relro_seg_t at tfibsegs: the segment is found by a closed computation over the image's segment list. *)
Lemma relro_seg_reply_A : YG0ncf.relro_seg_t (ci := CfImg_A) tfibsegs.
Proof.
unfold YG0ncf.relro_seg_t. split.
- assert (Hb : existsb (fun sg => (Z.of_N (seg_base sg) <=? cf_relro_lo) &&
    (cf_relro_hi <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) tfibsegs = true) by (vm_compute; reflexivity).
  destruct (proj1 (existsb_exists _ _) Hb) as (sg & Hsg & Hc).
  apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists sg. split; [exact Hsg | split; assumption].
- (* part 3c: each of the report's read-only reads (CfImg's cf_ro_reads) lies in one segment *)
  assert (Hb : forallb (fun r => existsb (fun sg => (Z.of_N (seg_base sg) <=? fst r) &&
    (fst r + snd r <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) tfibsegs) cf_ro_reads = true)
    by (vm_compute; reflexivity).
  apply Forall_forall. intros r Hr. pose proof (proj1 (forallb_forall _ _) Hb r Hr) as E. cbv beta in E.
  destruct (proj1 (existsb_exists _ _) E) as (sg & Hsg & Hc).
  apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists sg. split; [exact Hsg | split; assumption].
Qed.

(* 3. errno_relro_t at TfibSyms. *)
Lemma errno_relro_reply_A : forall B, TfibSyms B -> YG0ncf.errno_relro_t (ci := CfImg_A) B.
Proof.
intros B TS. unfold YG0ncf.errno_relro_t. rewrite (ts_errno B TS). cbn [cf_relro_lo cf_relro_hi cf_ro_reads CfImg_A].
unfold TFIB_ERRNO. split; [lia|].
repeat constructor; cbn [fst snd]; lia.
Qed.

(* 4. pf_ial_apart_t at TfibSyms. *)
Lemma pf_ial_apart_reply_A : forall B, TfibSyms B -> YG0ncf.pf_ial_apart_t (ci := CfImg_A) B.
Proof.
intros B TS a Ha. rewrite (ts_ial_lo B TS), (ts_ial_hi B TS), (ts_ial_flag B TS).
cbn [cf_toolname_cell cf_pfcb_cell CfImg_A] in Ha. unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG. lia.
Qed.

(* 5. DZONE's first disjunct by name (A/AFgi.v:484-485). *)
Definition dzone_static_lo : Z := TFIB_STORE.
Definition dzone_static_hi : Z := AD20.RS_LO.
Lemma dzone_static_text_A : forall ly a, AFgi.DZONE ly a =
((dzone_static_lo <= a < dzone_static_hi) \/ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/
 (ly_SB ly <= a < ly_SB ly + kStoreBlockSize)).
Proof. intros ly a. reflexivity. Qed.

(* 6. pf_cells_apart_t at TfibSyms. *)
Lemma pf_cells_apart_reply_A : forall B, TfibSyms B -> YG0ncf.pf_cells_apart_t (ci := CfImg_A) B.
Proof.
intros B TS a Ha. rewrite (ts_store B TS), (ts_oom B TS).
cbn [cf_toolname_cell cf_pfcb_cell cf_errbuf_obj CfImg_A] in Ha |- *. unfold TFIB_STORE, TFIB_OOM. lia.
Qed.

(* 7. The static half of PF_APART, from 6 at TfibB. *)
Lemma pf_dzone_static_reply_A : forall a, (cf_toolname_cell <= a < cf_toolname_cell + 8 \/ cf_pfcb_cell <= a < cf_pfcb_cell + 8) ->
~ (dzone_static_lo <= a < dzone_static_hi).
Proof.
intros a Ha [Hlo _]. destruct (pf_cells_apart_reply_A _ AD2l.TfibB_syms a Ha) as [H _]. rewrite (ts_store _ AD2l.TfibB_syms) in H. unfold dzone_static_lo in Hlo. lia.
Qed.

(* 8. zones_miss_relro_reply_A (field round 3 part 3; the statement is a Theorem Labs lane's, 18:21Z, agreed with DeallocNmaxA, whose
   lib/A/DGmpcf.v is to Require this file and close its zones_miss_relro by exact): the unit image row behind the
   Deallocate walks' keep law of arodata_ok_cf (cgif: DGmpcf.zones_miss_relro_cgif, proofs/cgif/
   cgif_file_fuzzer/lib/DGmpcf.v:82-117 at e8a7dd66acf; its proof with CfImg_cgif -> CfImg_A and YF0x -> AF0x). At the
   seed's geometry (DGgm.free_hyps), no non-owned byte of the RELRO range lies in the walk's window (DGif0.dwin_m), the
   depot zone (DGgi.DZONE), the internal allocator's zone (DGgi.IZONE) or the freed block's shadow (DGif0.dshadow).
   Part 3c: the covered set is YG0dcf.aro_addr_cf (the RELRO range and the report reads cf_ro_reads).
   Named bounds only: CfImg_A's cf_relro_lo / cf_relro_hi / cf_ro_reads, the zones' own Definitions, the image window
   AF0x.TFIB_IMG_LO / TFIB_IMG_END, and the seed's facts DGgm.LYB / derived_ranges / fh_Hsp / fh_Hp / N8_ge. *)
Section Z. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem zones_miss_relro_reply_A : forall (B : asyms) W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU, DGgm.free_hyps W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU -> forall a, YG0dcf.aro_addr_cf (ci := CfImg_A) a -> ~ Exists (in_zr a) (as_owned_static B) -> 0 <= a < 2 ^ 64 /\ ~ DGif0.dwin_m ly (bv_unsigned (getr regs0 2)) p a /\ ~ DGgi.DZONE ly a /\ ~ DGgi.IZONE a /\ ~ DGif0.dshadow p nn a.
Proof.
intros B W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH a Ha0 _.
(* part 3c: a covered address is in the RELRO range or in one of the report's read-only reads (cf_ro_reads), all of
   them in [AF0x.TFIB_IMG_LO, cf_relro_hi) *)
assert (Ha : AF0x.TFIB_IMG_LO <= a < @cf_relro_hi CfImg_A).
{ unfold YG0dcf.aro_addr_cf in Ha0. unfold AF0x.TFIB_IMG_LO. cbn [cf_relro_lo cf_relro_hi cf_ro_reads CfImg_A] in Ha0 |- *.
  destruct Ha0 as [Ha0|Ha0]; [lia|].
  apply Exists_exists in Ha0 as (r & Hr & Hin). cbn [In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; unfold in_zr in Hin; cbn [fst snd] in Hin; lia. }
clear Ha0. unfold AF0x.TFIB_IMG_LO in Ha. cbn [cf_relro_hi CfImg_A] in Ha.
pose proof (DGgm.LYB W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH)
  as (ZT & _ & _ & _ & _ & _ & _ & _ & ZNB & _ & ZSB & _ & _ & _ & _ & _ & HSTKLO).
pose proof (DGgm.derived_ranges W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH) as (DP & _ & DSP & _).
pose proof (DGgm.fh_Hsp W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH) as (S1 & _ & _).
pose proof (DGgm.fh_Hp W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH) as HP.
pose proof (DGgm.N8_ge W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH) as [N8a N8b].
assert (HIMG : AF0x.TFIB_IMG_LO <= a < AF0x.TFIB_IMG_END) by (unfold AF0x.TFIB_IMG_LO, AF0x.TFIB_IMG_END; lia).
assert (NDZ : ~ DGgi.DZONE ly a).
{ unfold DGgi.DZONE. intros [Hd|[Hd|Hd]].
  - lia.
  - exact (AF0x.zone3_apart_img _ _ a ZNB HIMG Hd).
  - exact (AF0x.zone3_apart_img _ _ a ZSB HIMG Hd). }
assert (NIZ : ~ DGgi.IZONE a) by (unfold DGgi.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG; lia).
assert (NWIN : ~ DGif0.dwin_m ly (bv_unsigned (getr regs0 2)) p a).
{ unfold DGif0.dwin_m, ImgBaseDG.DGgmC.WINT, ImgBaseDG.DGgmC.WINB, ImgBaseDG.DGbaseC.DFSTACK. cbv beta zeta.
  unfold DGbase.DFSTACK in S1. unfold kHighMemBeg in HSTKLO.
  intros [Hw|[[Hw|Hw]|[Hw|Hw]]].
  - lia.
  - exact (AF0x.zone3_apart_img _ _ a ZT HIMG ltac:(unfold t_unwinding, kThreadObjSize in *; lia)).
  - exact (AF0x.zone3_apart_img _ _ a ZT HIMG ltac:(unfold t_stats, kThreadObjSize in *; lia)).
  - exact (AF0x.zone3_apart_img _ _ a HP HIMG ltac:(lia)).
  - exact (AF0x.zone3_apart_img _ _ a HP HIMG ltac:(lia)). }
assert (NSH : ~ DGif0.dshadow p nn a)
  by (unfold DGgm.SPv in DSP; unfold DGif0.dshadow, ImgBaseDG.DGgiC.SPv, SHADOW_OFF in *; lia).
split; [lia|]. split; [exact NWIN|]. split; [exact NDZ|]. split; [exact NIZ | exact NSH].
Qed.
End Z.
