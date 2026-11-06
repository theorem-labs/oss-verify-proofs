(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "leb"; "pow"; "ltb"; "of_nat"; "to_nat"; "opp"; "modulo"; "mul"; "eqb"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "False"; "ex"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "cell"; "sobj"; "valuation"; "SLit"; "sprop"; "ob_base"; "ob_cells"; "eval"; "obj_holds"; "c_off"; "holds"; "mkCell"; "rom_ok"; "ob_hi"; "ob_lo"; "obj_range"; "rd"; "enc_bytes"; "image_byte"; "ob_dflt"; "odefault"; "rm"; "ro_addr"; "DImage"; "DZero"; "c_width"; "covered"; "ranges_disjoint"; "rw"; "@Corelib.Init.Datatypes"; "andb"; "bool"; "option"; "true"; "false"; "list"; "negb"; "Some"; "nat"; "orb"; "prod"; "fst"; "length"; "nil"; "snd"; "pair"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Pristine"; "reads"; "untouched"; "auxv_keys"; "pristine_req"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvPristine.P"; "outb"; "find_cell"; "PRm"; "robjs_miss"; "robjs_hi_img"; "cells_clear"; "cells_lit62"; "img_ok_rangeb"; "img_okb"; "robj_img"; "wseg_rangeb"; "PRvm"; "prm_fp"; "robj_img_misses"; "robjs_miss_statics"; "rom_bytes_ok"; "@Corelib.Lists.ListDef"; "Forall"; "nth"; "seq"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "find_segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "wz"; "mc_chk_guard"; "mc_chk_guard_got"; "mc_ctx"; "mc_ctz_tab"; "mc_lock"; "mc_med_cnt_tab"; "mc_replaced"; "mc_size_classes"; "mc_small_cnt_tab"; "topL"; "mc_libc"; "mc_errno"; "img_reserved"; "mc_auxv"; "mc_need_locks"; "mc_page_size"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_ok"; "img_ok"; "robj_stack"; "T0"; "aceil"; "caddr"; "robjs_ok"; "robjs_okF"; "@Stdlib.Lists.List"; "forallb"; "In"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "CTX_SIZE"; "layout"; "ly_brk0"; "ly_sec"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "seg_writable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "ri_sec"; "run_init"; "MA"; "ma_L"; "ri_top"; "ri_brk0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "PGSZ"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "alloc_top"; "m_vmmaps"; "vm_brk"; "vm_maps"; "vm_start_brk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvStatics"; "a_got"; "a_guard"; "a_nl"; "statics_disjoint"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "rd_of"; "tp_ok"; "wseg_addr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "auxv_init"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundL SymSoundM SymSoundI SymSoundR SymFrame SymEntail SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocLayout MallocIface MallocLaws Contract ContractI Pristine ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import TobjJV DrvStatics.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section P.
Variable segs : list Segment.
Variable C : mconsts.

Definition PRm (m : word -> option byte) (ri : run_init) (av q : Z) : Prop := ltac2:(tb__ "0|7|
SfS47Vm;S63VC;A1S7eA3SfS47Vm;S65VC;A1Z4M0A3SfS47Vm;S67VC;A1G0A3SfS47Vm;S6fVC;A1Z1A3SfS47Vm;S68VC;A1Z60A3SfS47Vm;S69VC;A1Z1bA3SfS47Vm;S66VC;A1G0A3SfS47Vm;S64VC;A1Z20A3SfS47Vm;S62VC;A1Z8M1A3SfS46Vsegs;Vm;S70VC;A1U8M2Z1000A5SfS13S0S0S46Vsegs;Vm;S61VC;A1G2R1A5Lgd;A2SfS46Vsegs;Vm;S6eVC;A1G2Vav;A5SfS3S88Vri;A1M3Vav;A2SfS3S4Vav;Za0A2S7Z2Z40A2M4A2SfS3G3Vq;A2SfS3S4Vq;Z10M5A2G4A2SfS3bS7dR1UaA2M6S46Vsegs;Vm;S4Vav;SdG5S9R2A1A2A2G2S5bS0R2S48Z0A4A5F_;Fj;SfS3bG6S13S0S0S46Vsegs;Vm;S4S4Vav;SdG5S9R3A1A2A2G1A2G2R1A5Lv;A2F_;Fj;SfS46Vsegs;Vm;S4Vav;Z88A2G2Vq;A5S46Vsegs;Vm;S4Vq;G1A2G2S84Vri;A1A5A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").

Lemma auxv_init_of_PRm : ltac2:(tb__ "0|2|
S18S7fS85S0S0S4cS2bR5A1R3R2R1A4S10S0ScR3Z8A2Z0A3M0G0S3S44Q40S32R8PaA2A2R5A2S3S4R6Za0A2R5A2S3S4R6Z10A2S7Z2Z30A2A2S10S0S81RaA1S84R9A1A3SfS3S8aS80RbA1M1A2S5G1Z2aaaaaaa9000A2A2S98Vsegs;VC;RcRdA4F_;F_;F_;F_;F_;F_;F_;F_;Fq;Fav;Fri;FL;Frho;").
Proof using .
  intros rho L ri av q H Hav Hq Hsp Hd Hq16 Hsec Hbrk. unfold PRm in H.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rav & _ & _ & _ & _ & Rkeys & Rvals & Rq & Rsec).
  exists av, q. split; [exact Rav|]. split; [exact Rkeys|]. split; [exact Rvals|]. split; [exact Rq|].
  split; [rewrite Hsec; exact Rsec|]. repeat (split; [lia|]). lia.
Qed.

Definition PRvm (ri : run_init) (md : Model) : Prop := ltac2:(tb__ "0|8|
S89Vri;A1S0SfS10S38S3dS43Q40M0A1M1G1A2M2A1S8fS8dVmd;A1M3A1S40G2A1A3SfS10S0S44G0S8eG3A1A2R1A3SfS10S0S44G0S90G3A1A2R1A3SfS10S0ScR1S8aA2Z0M4A3SfSfS10S0S8cG3A1S88Vri;A1M5A3SfSfS3Z7fff7f800000M6G5A2S3G5Z7fffff800000A2A2SfS3G4S84Vri;A1M7A2S5G7S7Z2Z40A2A2A2A2A2SfSfS5G4R1A2S5R1Z2aaaaaaa9000A2A2S6dVC;G3A2A2A2A2A2A2A2Tbrk0;").

Lemma PRm_pristine : ltac2:(tb__ "0|0|
S85S18S8bS0S0S4cS2bR4A1R5R2R1A4S55R6R4A2S96VC;R6A2S49Vsegs;VC;R8R7R6A5F_;F_;F_;Fq;Fav;Fmd;Frho;Fri;").
Proof using .
  intros ri rho md av q H (V1 & V2 & V3 & V4 & V5 & V6 & V7) HT. unfold PRm in H. unfold pristine_req. cbn zeta.
  assert (V6' : 0 < ri_brk0 ri /\ ri_brk0 ri < 140735332483072) by (destruct V6 as [V6a V6b]; split; lia).
  decompose [and] H.
  repeat (split; [assumption|]).
  split; [exists av, q; repeat (split; [assumption|]); assumption|].
  repeat (split; [assumption|]). exact HT.
Qed.

Definition prm_fp (av q a : Z) : Prop := ltac2:(tb__ "0|c|
S11SfS3S63VC;A1M0Va;A2S5Va;S4G0S7eA2A2A2S11SfS3S65VC;A1M1Va;A2S5Va;S4G1Z4M2A2A2A2S11SfS3S67VC;A1M3Va;A2S5Va;S4G3G2A2A2A2S11SfS3S6bVC;A1M4Va;A2S5Va;S4G4Z38A2A2A2S11SfS3S68VC;A1M5Va;A2S5Va;S4G5Z60A2A2A2S11SfS3S69VC;A1M6Va;A2S5Va;S4G6Z1bA2A2A2S11SfS3S66VC;A1M7Va;A2S5Va;S4G7G2A2A2A2S11SfS3S64VC;A1M8Va;A2S5Va;S4G8Z20A2A2A2S11SfS3S62VC;A1M9Va;A2S5Va;S4G9Z8MaA2A2A2S11SfS3S61VC;A1MbVa;A2S5Va;S4GbGaA2A2A2S11SfS3Vav;Va;A2S5Va;S4Vav;Za0A2A2A2SfS3S4Vq;GaA2Va;A2S5Va;S4Vq;Z10A2A2A2A2A2A2A2A2A2A2A2A2A2A2").

Lemma reads_ext : ltac2:(tb__ "0|3|
S43Q40A1S35S43Q8A1A1M0Fx;M1G1S0S3bS0S3bS7dR1R3A2S10G0R6S60S4R5S9R2A1A2A1M2A1R7G2A1A3F_;Fk;S46Vsegs;R6R4R3R2A5S46Vsegs;R6R5R4R3A5F_;F_;Fv;Fw;Fa;Fm';Fm;").
Proof using . intros m m' a w v E H k Hk. unfold rd_of. rewrite (E k Hk). apply (H k Hk). Qed.

Lemma untouched_ext : ltac2:(tb__ "0|3|
S43Q40A1S35S43Q8A1A1M0F_;M1G1S0S0S0SfS3R3R1A2S5R1S4R3R2A2A2A2S10G0R5S60R2A1M2A1R6G2A1A3F_;Fa;S47R5R3R2A3S47R5R4R3A3F_;F_;Fn;Flo;Fm';Fm;").
Proof using . intros m m' lo n E H a Ha. rewrite (E a Ha). apply H. exact Ha. Qed.

Lemma PRm_ext : ltac2:(tb__ "0|3|
S43Q40A1S35S43Q8A1A1M0Fx;M1G1S85S0S0S0S56R3R2R1A3S10G0R6S60R2A1M2A1R7G2A1A3F_;Fa;S4cR6R4R3R2A4S4cR6R5R4R3A4F_;F_;Fq;Fav;Fri;Fm';Fm;").
Proof using .
  intros m m' ri av q E H. unfold PRm in H |- *.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & [gd H11] & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20).
  assert (U : forall lo n, (forall a, lo <= a < lo + n -> prm_fp av q a) -> untouched m lo n -> untouched m' lo n).
  { intros lo n Hfp Hu. eapply untouched_ext; [|exact Hu]. intros a Ha. apply E. apply Hfp. exact Ha. }
  assert (R : forall a w v, (forall k, (k < w)%nat -> prm_fp av q (a + Z.of_nat k)) -> reads segs m a w v -> reads segs m' a w v).
  { intros a w v Hfp Hr. eapply reads_ext; [|exact Hr]. intros k Hk. apply E. apply Hfp. exact Hk. }
  unfold prm_fp in U, R. unfold mc_need_locks, mc_page_size, mc_auxv in *.
  split; [apply U; [intros; lia|exact H1]|]. split; [apply U; [intros; lia|exact H2]|]. split; [apply U; [intros; lia|exact H3]|].
  split; [apply U; [intros; lia|exact H4]|]. split; [apply U; [intros; lia|exact H5]|]. split; [apply U; [intros; lia|exact H6]|].
  split; [apply U; [intros; lia|exact H7]|]. split; [apply U; [intros; lia|exact H8]|]. split; [apply U; [intros; lia|exact H9]|].
  split; [apply R; [intros; lia|exact H10]|]. split; [exists gd; apply R; [intros; lia|exact H11]|].
  split; [apply R; [intros; lia|exact H12]|]. split; [exact H13|]. split; [exact H14|]. split; [exact H15|]. split; [exact H16|].
  split; [intros j Hj; apply R; [intros; lia|exact (H17 j Hj)]|].
  split; [intros j Hj; destruct (H18 j Hj) as [v Hv]; exists v; apply R; [intros; lia|exact Hv]|].
  split; [apply R; [intros; lia|exact H19]|]. apply R; [intros; lia|exact H20].
Qed.

Definition img_okb (a : Z) : bool := ltac2:(tb__ "0|d|
S33S33S33S33S33S33S33S33S33S33S33S97Vsegs;S45Q40Va;A2A2S39S33S6S63VC;A1M0Va;A2S8Va;S4G0S7eA2A2A2A1A2S39S33S6S65VC;A1M1Va;A2S8Va;S4G1Z4M2A2A2A2A1A2S39S33S6S6cVC;A1M3Va;A2S8Va;S4G3G2A2A2A2A1A2S39S33S6S6bVC;A1M4Va;A2S8Va;S4G4Z38A2A2A2A1A2S39S33S6S67VC;A1M5Va;A2S8Va;S4G5G2A2A2A2A1A2S39S33S6S68VC;A1M6Va;A2S8Va;S4G6Z60A2A2A2A1A2S39S33S6S69VC;A1M7Va;A2S8Va;S4G7Z1bA2A2A2A1A2S39S33S6S66VC;A1M8Va;A2S8Va;S4G8G2A2A2A2A1A2S39S33S6S64VC;A1M9Va;A2S8Va;S4G9Z20A2A2A2A1A2S39S33S6S62VC;A1MaVa;A2S8Va;S4GaZ8MbA2A2A2A1A2S39S33S6S61VC;A1McVa;A2S8Va;S4GcGbA2A2A2A1A2").

Lemma nrangeb : ltac2:(tb__ "0|0|
S0S0S0S10S34S39S33S6R3R1A2S8R1R2A2A2A1S36A3S14SfS3R4R2A2S5R2R3A2A2A1F_;Fa;Fhi;Flo;").
Proof using .
  intros lo hi a H [H1 H2]. apply Bool.negb_true_iff in H. apply Bool.andb_false_iff in H as [H|H].
  - apply Z.leb_gt in H. lia. - apply Z.ltb_ge in H. lia.
Qed.

Lemma img_okb_sound : ltac2:(tb__ "0|0|
S0S10S34S52R1A1S36A3S74Vsegs;VC;R2A3F_;Fa;").
Proof using .
  intros a H. unfold img_okb in H.
  repeat (apply andb_prop in H; destruct H as [H ?]).
  repeat match goal with K : negb _ = true |- _ => apply nrangeb in K end.
  unfold img_ok, errno_range, static_range. split; [exact H|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  intros X. decompose [or] X; contradiction.
Qed.

Fixpoint wseg_rangeb (ss : list Segment) (lo hi : Z) : bool :=
  if hi <=? lo then true else
  match ss with
  | [] => false
  | seg :: rest =>
    let base := Z.of_N (seg_base seg) in
    let top := base + Z.of_N (seg_size seg) in
    let ilo := Z.max lo base in
    let ihi := Z.min hi top in
    if ilo <? ihi
    then seg_writable seg && wseg_rangeb rest lo ilo && wseg_rangeb rest ihi hi
    else wseg_rangeb rest lo hi
  end.

Lemma wseg_rangeb_sound : ltac2:(tb__ "0|0|
S38S82A1S0S0S0S10S34S54R4R3R2A3S36A3SfS3R4R2A2S5R2R3A2A2S10S34S35S82A1S34Lx;S5fR6R3Z1A3S82S83R1A1Lseg;S37X35x2S36A3F_;F_;Fa;Fhi;Flo;Fss;").
Proof using .
  induction ss as [|seg rest IH]; intros lo hi a H Ha.
  - cbn in H. destruct (hi <=? lo) eqn:E; [apply Z.leb_le in E; lia|discriminate].
  - cbn [wseg_rangeb] in H. destruct (hi <=? lo) eqn:E; [apply Z.leb_le in E; lia|]. clear E.
    cbn [find_segment]. cbv zeta in H.
    set (base := Z.of_N (seg_base seg)) in *. set (top := base + Z.of_N (seg_size seg)) in *.
    destruct (Z.max lo base <? Z.min hi top) eqn:EI.
    + apply Z.ltb_lt in EI.
      apply andb_prop in H as [H H3]. apply andb_prop in H as [Hw H2].
      destruct (Z.leb base a && Z.leb (a + 1) top) eqn:ET.
      * exact Hw.
      * apply Bool.andb_false_iff in ET as [ET|ET]; apply Z.leb_gt in ET.
        -- apply (IH lo (Z.max lo base) a H2). lia.
        -- apply (IH (Z.min hi top) hi a H3). lia.
    + apply Z.ltb_ge in EI.
      destruct (Z.leb base a && Z.leb (a + 1) top) eqn:ET.
      * apply andb_prop in ET as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
      * apply (IH lo hi a H Ha).
Qed.

Definition outb (x n lo hi : Z) : bool := ltac2:(tb__ "0|0|
S3cS6Vhi;Vx;A2S6S4Vx;Vn;A2Vlo;A2A2").

Lemma outb_sound : ltac2:(tb__ "0|0|
S0S0S0S0S0S10S34S4aR5R4R3R2A4S36A3SfS3R4R2A2S5R2R3A2A2S10S34S39S33S6R7R3A2S8R3S4R7R6A2A2A2A1S36A3F_;F_;Fa;Fhi;Flo;Fn;Fx;").
Proof using .
  intros x n lo hi a H Ha. unfold outb in H. apply Bool.negb_true_iff. apply Bool.andb_false_iff.
  apply Bool.orb_true_iff in H as [H|H]; apply Z.leb_le in H.
  - left. apply Z.leb_gt. lia.
  - right. apply Z.ltb_ge. lia.
Qed.

Definition img_ok_rangeb (lo hi : Z) : bool := ltac2:(tb__ "0|2|
S3cS6Vhi;Vlo;A2S33S33S33S33S33S33S33S33S33S33S33S54Vsegs;Vlo;Vhi;A3S4aS63VC;A1S7eVlo;Vhi;A4A2S4aS65VC;A1Z4M0Vlo;Vhi;A4A2S4aS6cVC;A1G0Vlo;Vhi;A4A2S4aS6bVC;A1Z38Vlo;Vhi;A4A2S4aS67VC;A1G0Vlo;Vhi;A4A2S4aS68VC;A1Z60Vlo;Vhi;A4A2S4aS69VC;A1Z1bVlo;Vhi;A4A2S4aS66VC;A1G0Vlo;Vhi;A4A2S4aS64VC;A1Z20Vlo;Vhi;A4A2S4aS62VC;A1Z8M1Vlo;Vhi;A4A2S4aS61VC;A1G1Vlo;Vhi;A4A2A2").

Lemma img_ok_rangeb_sound : ltac2:(tb__ "0|0|
S0S0S0S3Z0R3A2S3R3S7Z2Z40A2A2S10S34S51R5R4A2S36A3SfS3R6R4A2S5R4R5A2A2S10S34S52R5A1S36A3F_;F_;F_;F_;Fa;Fhi;Flo;").
Proof using .
  intros lo hi a H0 H64 H Ha. unfold img_ok_rangeb in H.
  apply Bool.orb_true_iff in H as [H|H]; [apply Z.leb_le in H; lia|].
  repeat (apply andb_prop in H; destruct H as [H ?]).
  unfold img_okb.
  repeat match goal with K : outb _ _ lo hi = true |- _ => apply (fun K' => outb_sound _ _ lo hi a K' Ha) in K; rewrite K; clear K end.
  rewrite !Bool.andb_true_r.
  unfold wseg_addr.
  replace (bv_unsigned (Z_to_bv 64 a)) with a.
  - exact (wseg_rangeb_sound segs lo hi a H Ha).
  - rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. unfold bv_modulus. lia.
Qed.

Definition robj_img (o : sobj) : bool := ltac2:(tb__ "0|8|
S15S34Lx;M0S1bVo;A1S0S0S34Lz;R1G0S24Vo;A1S0G0S23Vo;A1S0S33S33S33S6Z0R2A2S6R2R1A2A2S8R1S7Z2Z3eA2A2A2S51R2R1A2A2Lhi;S1S37Li;M1S71S15S15S37Lb;La;M2Lop;M3G3S72G2Lop;M4G4S34S2S15S37La;Lw;Lsgn;M5S1S15S0S37Lk;Li;Ll;M6X15x8Llo;G1G3G3G4G4G5G6X15x8S1S37Lp;M7G7X0x3Lz;G1G3G3G4G4G5G6X15x8").

Lemma robj_img_sound : ltac2:(tb__ "0|1|
S18S17S0S10S34S53R2A1S36A3SfS3S3eS0S0S25R4R3A2M0A3R2A2S5R2S41S0S0G0A3A2A2S74Vsegs;VC;R3A3F_;F_;Fa;Fo;Frho;").
Proof using .
  intros rho o a H Hr. unfold robj_img in H.
  destruct (ob_base o) as [b| | | | | | |] eqn:Eb; try discriminate. destruct b; try discriminate.
  destruct (ob_lo o) as [lo| | | | | | |] eqn:El; try discriminate.
  destruct (ob_hi o) as [hi| | | | | | |] eqn:Eh; try discriminate.
  apply andb_prop in H as [H Hf]. apply andb_prop in H as [H H1]. apply andb_prop in H as [H0 H2].
  apply Z.leb_le in H0. apply Z.ltb_lt in H1. apply Z.leb_le in H2.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Eb, El, Eh in Hr. cbn [fst snd eval] in Hr.
  replace (bv_unsigned (Z_to_bv 64 0)) with 0 in Hr by reflexivity.
  rewrite !soff_lit_small in Hr by lia.
  apply img_okb_sound. apply (img_ok_rangeb_sound lo hi a); [lia|lia|exact Hf|lia].
Qed.

Definition robjs_hi_img (facts : list sprop) (objs : list sobj) : bool := ltac2:(tb__ "0|0|
S7bS17S17S34S34L_;S75Vfacts;R1A2S36S53R1A1X34x2Lo;Vobjs;A3").

Lemma robjs_hi_img_caddr : ltac2:(tb__ "0|1|
S18S38S1aA1S38S17A1S86S35S0A1S5aS1aS20R5A1R4A3S73R6S6aS87R3A1A1A2S10S34S4eR6R5A2S36A3S17S0S7cS17R2R8A3SfS3S3eS0S0S25RbR3A2M0A3R2A2S5R2S41S0S0G0A3A2A2S78Vsegs;VC;R9R8R3A5F_;F_;Fa;Fo;F_;F_;F_;Fx;FAi;Fobjs;Ffacts;Frho;").
Proof using .
  intros rho facts objs Ai x HF HT H o a Ho Hr.
  pose proof (proj1 (forallb_forall _ _) H o Ho) as Hc. cbn beta in Hc. apply lazy_orb_prop in Hc as [Hc|Hc].
  - left. exact (robj_stack_sound facts rho _ o a HF HT Hc Hr).
  - right; left. exact (robj_img_sound rho o a Hc Hr).
Qed.

Corollary robjs_hi_img_ok : ltac2:(tb__ "0|0|
S18S38S1aA1S38S17A1S86S35S0A1S5aS1aS20R5A1R4A3S73R6S6aS87R3A1A1A2S10S34S4eR6R5A2S36A3S79Vsegs;VC;R5R4R8R6A6F_;F_;F_;Fx;FAi;Fobjs;Ffacts;Frho;").
Proof using . intros rho facts objs Ai x HF HT H o a Ho Hr. exact (robjs_hi_img_caddr rho facts objs Ai x HF HT H o a Ho Hr). Qed.

Corollary robjs_hi_img_okF : ltac2:(tb__ "0|0|
S18S38S3dS0S0A2A1S18S38S1aA1S38S17A1S38S3dS15S15A2A1S5aS1aS20R4A1R3A3S73R5S76R7A1A2S10S34S4eR5R4A2S36A3S7aVsegs;VC;R9R8R7R4R5A7F_;F_;F_;Fkept;Fobjs;Ffacts;Frho;FFB;Frho0;").
Proof using .
  intros rho0 FB rho facts objs kept HF HT H o a Ho Hr.
  pose proof (proj1 (forallb_forall _ _) H o Ho) as Hc. cbn beta in Hc. apply lazy_orb_prop in Hc as [Hc|Hc].
  - left. exact (robj_stack_sound facts rho _ o a HF HT Hc Hr).
  - right; left. exact (robj_img_sound rho o a Hc Hr).
Qed.

Definition robj_img_misses (lo hi : Z) (o : sobj) : bool := ltac2:(tb__ "0|e|
S15S34Lx;M0S1bVo;A1S0G0S24Vo;A1S0G0S23Vo;A1S0S33S33S33S33S33S6Z0M1R3A2S8R3S7Z2Z3eA2M2A2A2S6G1S4R3R2A2M3A2A2S6R2R1A2A2S8S4R3R1A2M4G2A2A2S3cS3cS3cS6G4G3A2S6Vhi;Vlo;A2A2S6G4Vlo;A2A2S6Vhi;G3A2A2A2Lohi;S1S37Li;M5S71S15S15S37Lb0;La;M6Lop;M7G7S72G6Lop;M8G8S34S2S15S37La;Lw;Lsgn;M9S1S15S0S37Lk;Li;Ll;MaX15x8Lolo;G5G7G7G8G8G9GaX15x8Lb;G5S71S15S15S37Lb;La;MbLop;McGcS72GbLop;MdGdG9GaX15x8").

Definition robjs_miss (facts : list sprop) (lo hi : Z) (objs : list sobj) : bool := ltac2:(tb__ "0|0|
S33S6Vhi;S77A2S7bS17S17S34S34L_;S75Vfacts;R1A2S36S57Vlo;Vhi;R1A3X34x2Lo;Vobjs;A3A2").

Lemma robjs_miss_sound : ltac2:(tb__ "0|0|
S18S38S1aA1S0S0S38S17A1S7fS5aS1aS20R6A1R5A3S73R7S6aR2A1A2S10S34S4dR7R6R5R4A4S36A3S5aS17S17S31S25RaR1A2S42S0S0R8R7A4A2Lo;R5A3F_;F_;F_;FL;Fobjs;Fhi;Flo;Ffacts;Frho;").
Proof using .
  intros rho facts lo hi objs L HF HT H. pose proof (topL_range L) as TR. apply andb_prop in H as [Hhi H]. apply Z.leb_le in Hhi. unfold aceil in Hhi.
  apply Forall_forall. intros o Ho.
  pose proof (proj1 (forallb_forall _ _) H o Ho) as Hc. cbn beta in Hc. apply lazy_orb_prop in Hc as [Hc|Hc].
  - unfold SymState.ranges_disjoint. cbn [fst snd].
    destruct (Z_lt_dec (fst (obj_range rho o)) (snd (obj_range rho o))); [|lia].
    pose proof (robj_stack_sound facts rho _ o (fst (obj_range rho o)) HF HT Hc ltac:(lia)). lia.
  - unfold robj_img_misses in Hc.
    destruct (ob_base o) as [b| | | | | | |] eqn:Eb; try discriminate.
    destruct (ob_lo o) as [olo| | | | | | |] eqn:El; try discriminate.
    destruct (ob_hi o) as [ohi| | | | | | |] eqn:Eh; try discriminate.
    apply andb_prop in Hc as [Hc Q6]. apply andb_prop in Hc as [Hc Q5]. apply andb_prop in Hc as [Hc Q4].
    apply andb_prop in Hc as [Hc Q3]. apply andb_prop in Hc as [Q1 Q2].
    apply Z.leb_le in Q1. apply Z.ltb_lt in Q2. apply Z.leb_le in Q3. apply Z.leb_le in Q4. apply Z.ltb_lt in Q5.
    unfold obj_range, obj_lo_of, obj_hi_of. rewrite Eb, El, Eh. cbn [fst snd eval].
    rewrite (Z_to_bv_small 64 b) by (rewrite two64; lia).
    unfold SymState.ranges_disjoint. cbn [fst snd].
    rewrite !soff_lit_small by lia. rewrite !Bool.orb_true_iff in Q6. rewrite !Z.leb_le in Q6. lia.
Qed.

Definition robjs_miss_statics (facts : list sprop) (objs : list sobj) : bool := ltac2:(tb__ "0|4|
S33S33S4dVfacts;S91VC;A1M0S4G0Z8M1A2Vobjs;A4S4dVfacts;S92VC;A1M2S4G2G1A2Vobjs;A4A2S4dVfacts;S93VC;A1M3S4G3Z1A2Vobjs;A4A2").

Lemma robjs_miss_statics_sound : ltac2:(tb__ "0|0|
S18S38S1aA1S38S17A1S7fS5aS1aS20R4A1R3A3S73R5S6aR2A1A2S10S34S58R5R4A2S36A3S94VC;R7R5A3F_;F_;F_;FL;Fobjs;Ffacts;Frho;").
Proof using .
  intros rho facts objs L HF HT H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  split; [|split]; eapply robjs_miss_sound; eauto.
Qed.

Fixpoint find_cell (cells : list cell) (off : Z) : option cell :=
  match cells with
  | [] => None
  | c :: rest => match c_off c with
                 | SLit o => if o =? off then Some c else find_cell rest off
                 | _ => find_cell rest off
                 end
  end.

Lemma find_cell_In : ltac2:(tb__ "0|0|
S38S16A1S0S16S10S35S16A1S4bR3R2A2S3aS16R1A2A3SfS7cS16R2R4A3S10S15S1fR2A1S19R3A1A3A2F_;Fc;Foff;Fcells;").
Proof using .
  induction cells as [|c0 rest IH]; intros off c H; cbn in H; [discriminate|].
  destruct (c_off c0) as [o| | | | | | |] eqn:E; try (destruct (IH _ _ H) as [A B]; split; [right; exact A|exact B]).
  destruct (Z.eqb_spec o off).
  - injection H as <-. split; [left; reflexivity|]. rewrite E. subst. reflexivity.
  - destruct (IH _ _ H) as [A B]. split; [right; exact A|exact B].
Qed.

Lemma held_cell_bytes : ltac2:(tb__ "0|3|
S18S5dS17S0S0S15S1eVsegs;R6R5R4A4S10S15S1bR5A1S19Z0M0A1A3S10S35S16A1S4bS1cR6A1R5A2S3aS16S21S19R5A1R4R3A3A2A3S3G0R6A2S3S4R7R6A2S7Z2Z3eA2A2S3G0R7A2S3bS7dR1SaR9A1A2S10S35S43Q8M1A1M2A1S26RdS45Q40S4RbS9R2A1A2A2A2S3aG2S5bG2R2S27SaRaA1S1dReR9A2A2S45G1G0A2A4A2A3F_;Fj;F_;F_;F_;F_;F_;F_;Fv;Fw;Foff;Fo;Fms;Frho;").
Proof using .
  intros rho ms o off w v Hoh Hb Hf Hoff How Hw j Hj.
  destruct (find_cell_In _ _ _ Hf) as [Hin _].
  destruct Hoh as (_ & _ & Hc & _). pose proof (proj1 (Forall_forall _ _) Hc _ Hin) as CH. rewrite Hb in CH.
  pose proof (cell_holds_bytes rho (SLit 0) _ _ ms off w v CH ltac:(lia)
                ltac:(cbn [eval]; replace (bv_unsigned (Z_to_bv 64 0)) with 0 by reflexivity; lia)
                ltac:(cbn [eval]; replace (bv_unsigned (Z_to_bv 64 0)) with 0 by reflexivity; lia) Hw j Hj) as R.
  cbn [eval] in R. replace (bv_unsigned (Z_to_bv 64 0)) with 0 in R by reflexivity. rewrite Z.add_0_l in R. exact R.
Qed.

Lemma crd_of_eq_rd : ltac2:(tb__ "0|2|
S5dS43Q40A1M0S35S43Q8A1A1M1F_;G0S22Vsegs;R3A2S10G1R3R2A1S5eR4R2A2A3S10G1S95Vsegs;R4R3A3S26R5R3A2A3F_;F_;Fa;Fm;Fms;").
Proof using .
  intros ms m a Hrom E. unfold Contract.rd_of, rd, ms_read_byte. rewrite E.
  destruct (ms_mem ms a); [reflexivity|]. symmetry. apply Hrom.
Qed.

Lemma held_cell_reads : ltac2:(tb__ "0|5|
S18S5dS43Q40A1S35S43Q8A1A1M0F_;S17S0S0S0S1eVsegs;R7R6R4A4S10S15S1bR5A1S19Z0M1A1A3S22Vsegs;R8A2S10S35S16A1S4bS1cR7A1R6A2S3aS16S21S19R6A1R5S19R4A1A3A2A3S3G1R7A2S3S4R8R7A2S7Z2M2Z3eA2A2SfS3G1R8A2M3S3R8Z8A2A2SfG3S5R8S7G2Z40A2A2A2S0SfS3RcR1A2S5R1S4RcRbA2A2A2S10G0RfS60R2A1M4A1S5eR10G4A2A3F_;Fa;S46Vsegs;ReRcSaRbA1RaA5F_;F_;F_;F_;F_;F_;F_;F_;F_;Fz;Fw;Foff;Fo;Fm;Fms;Frho;").
Proof using .
  intros rho ms m o off w z Hoh Hb Hrom Hf Hoff How Hw Hz Hm k Hk.
  unfold wz. rewrite (crd_of_eq_rd ms m (Z_to_bv 64 (off + Z.of_nat k)) Hrom) by (apply (Hm (off + Z.of_nat k)); lia).
  rewrite (held_cell_bytes rho ms o off w (SLit z) Hoh Hb Hf Hoff How ltac:(lia) k Hk).
  cbn [eval]. rewrite nth_enc_bytes by lia. reflexivity.
Qed.

Lemma held_cell_reads_sv : ltac2:(tb__ "0|4|
S18S5dS43Q40M0A1S35S43Q8A1A1M1F_;S17S0S0S15S1eVsegs;R7R6R4A4S10S15S1bR5A1S19Z0M2A1A3S22Vsegs;R8A2S10S35S16A1S4bS1cR7A1R6A2S3aS16S21S19R6A1R5R4A3A2A3S3G2R7A2S3S4R8R7A2S7Z2Z3eA2A2SfS3G2R8A2S3R8Z8A2A2S0SfS3RbR1A2S5R1S4RbRaA2A2A2S10G1ReS60R2A1M3A1S5eRfG3A2A3F_;Fa;S46Vsegs;RdRbSaRaA1S44G0S1dRfR9A2A2A5F_;F_;F_;F_;F_;F_;F_;F_;Fv;Fw;Foff;Fo;Fm;Fms;Frho;").
Proof using .
  intros rho ms m o off w v Hoh Hb Hrom Hf Hoff How Hw Hm k Hk.
  unfold wz. rewrite (crd_of_eq_rd ms m (Z_to_bv 64 (off + Z.of_nat k)) Hrom) by (apply (Hm (off + Z.of_nat k)); lia).
  rewrite (held_cell_bytes rho ms o off w v Hoh Hb Hf Hoff How ltac:(lia) k Hk).
  rewrite <- (Z_to_bv_bv_unsigned 64 (eval rho v)) at 1. rewrite nth_enc_bytes by lia. reflexivity.
Qed.

Lemma held_cell_bytes_b : ltac2:(tb__ "0|6|
S18S5dS17S0S0S0S15S1eVsegs;R7R6R5A4S10S0S44Q40M0S1dR8S1bR6A1A2A2R5A3S10S35S16A1S4bS1cR7A1R5A2S3aS16S21S19R5A1R4R3A3A2A3S3SbS7Z2M1Z3eA2M2A1R6A2S3Z0M3S4R8R7A2A2S3S4S4R9R8A2R7A2S7G1Z40A2A2S3R9G2A2S3G3R9A2S3bS7dR1SaRbA1A2S10S35S43Q8M4A1M5A1S26R10S45G0S4S4ReRdA2S9R2A1A2A2A2S3aG5S5bG5R2S27SaRcA1S1dR11RbA2A2S45G4G3A2A4A2A3F_;Fj;F_;F_;F_;F_;F_;F_;F_;F_;Fv;Fw;Foff;Fb;Fo;Fms;Frho;").
Proof using .
  intros rho ms o b off w v Hoh Hb Hf Ho1 Ho2 Ho3 Ho4 Hw j Hj.
  destruct (find_cell_In _ _ _ Hf) as [Hin _].
  destruct Hoh as (_ & _ & Hc & _). pose proof (proj1 (Forall_forall _ _) Hc _ Hin) as CH.
  pose proof (cell_holds_bytes rho (ob_base o) _ _ ms off w v CH ltac:(lia) ltac:(rewrite Hb; lia) ltac:(rewrite Hb; lia) Hw j Hj) as R.
  rewrite Hb in R. exact R.
Qed.

Lemma held_cell_reads_b : ltac2:(tb__ "0|7|
S18S5dS43Q40M0A1S35S43Q8A1A1M1F_;S17S0S0S0S15S1eVsegs;R8R7R5A4S10S0S44G0S1dR9S1bR6A1A2A2R5A3S22Vsegs;R9A2S10S35S16A1S4bS1cR8A1R6A2S3aS16S21S19R6A1R5R4A3A2A3S3SbS7Z2M2Z3eA2M3A1R7A2S3Z0M4S4R9R8A2A2S3S4S4RaR9A2R8A2S7G2Z40A2A2S3RaG3A2SfS3G4RaA2S3RaZ8A2A2S0SfS3S4ReRdA2M5R1A2S5R1S4G5RcA2A2A2S10G1R11S60R2A1M6A1S5eR12G6A2A3F_;Fa;S46Vsegs;R10G5SaRcA1S44G0S1dR12RbA2A2A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fv;Fw;Foff;Fb;Fo;Fm;Fms;Frho;").
Proof using .
  intros rho ms m o b off w v Hoh Hb Hrom Hf Ho1 Ho2 Ho3 Ho4 Hw Hm k Hk.
  unfold wz. rewrite (crd_of_eq_rd ms m (Z_to_bv 64 (b + off + Z.of_nat k)) Hrom) by (apply (Hm (b + off + Z.of_nat k)); lia).
  rewrite (held_cell_bytes_b rho ms o b off w v Hoh Hb Hf Ho1 Ho2 Ho3 Ho4 ltac:(lia) k Hk).
  rewrite <- (Z_to_bv_bv_unsigned 64 (eval rho v)) at 1. rewrite nth_enc_bytes by lia. reflexivity.
Qed.

Lemma held_zero_reads : ltac2:(tb__ "0|5|
S18S5dS43Q40M0A1S35S43Q8A1A1M1F_;S17S0S0S0S0S3bS1eVsegs;R9R8R6A4S10S0S44G0S1dRaS1bR7A1A2A2R6A3S22Vsegs;RaA2S10S15S24R9A1S19R7A1M2A3S10S15S23RaA1G2A3S10S2aS29RbA1S2eA3S10S38S16A1S1cRcA1S40S16A1A3S3SbS7Z2Z3eA2M3A1RbA2S3RbG3A2S3S4ReRdA2RbA2S3S4RcS9RbA1A2S4RfRdA2A2S0SfS3ReR1A2S5R1S4ReS9RdA1A2A2A2S10G1R14S60R2A1M4A1S5eR15G4A2A3F_;Fx;S46Vsegs;R13ReRdZ0A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Fa;Fhi;Flo;Fb;Fo;Fm;Fms;Frho;").
Proof using .
  intros rho ms m o b lo hi a w Hoh Hb Hrom Hlo Hhi Hd Hc L1 L2 Ha1 Ha2 Hm k Hk.
  unfold wz. rewrite (crd_of_eq_rd ms m (Z_to_bv 64 (a + Z.of_nat k)) Hrom) by (apply (Hm (a + Z.of_nat k)); lia).
  destruct Hoh as (Hrng & _ & _ & Hdf & _). unfold obj_lo_of, obj_hi_of in Hdf, Hrng. rewrite Hlo, Hhi, Hd, Hc in Hdf. rewrite Hlo, Hhi in Hrng.
  rewrite !soff_lit_small in Hdf, Hrng by lia. rewrite Hb in Hdf, Hrng.
  specialize (Hdf (a + Z.of_nat k - b) ltac:(lia) ltac:(intros X; inversion X)). cbn [dflt_holds] in Hdf.
  replace (b + (a + Z.of_nat k - b)) with (a + Z.of_nat k) in Hdf by lia. rewrite Hdf. rewrite le_byte_0. reflexivity.
Qed.

Definition cells_clear (cells : list cell) (lo n : Z) : bool := ltac2:(tb__ "0|3|
S7bS16S16S15S34Lx;S1fR1A1S0S3cS6S4R1S2fR2A1A2Vlo;A2S6S4Vlo;Vn;A2R1A2A2Lo;S1S37Li;S71S15S15S37Lb;La;M0Lop;M1G1S72G0Lop;M2G2S34S2S15S37La;Lw;Lsgn;S1S15S0S37Lk;Li;Ll;X15x8Lc;Vcells;A3").

Lemma cells_clear_sound : ltac2:(tb__ "0|4|
S18S38S16A1S0S0S0S10S34S4fR4R3R2A3S36A3SfS3R4R2A2S5R2S4R4R3A2A2A2S5aS16S16S15OLx;S1fR1A1S0SfS3SbS7Z2Z3eA2M0A1R1A2S3R1G0A2A2Lo;S1S12Li;S71S15S15S12Lb;La;M1Lop;M2G2S72G1Lop;M3G3S34S2S15S12La;Lw;Lsgn;S1S15S0S12Lk;Li;Ll;X15x8Lc;R6A3S14S30R8R7R4A3A1F_;F_;F_;Foff;Fn;Flo;Fcells;Frho;").
Proof using .
  intros rho cells lo n off H Hoff Hlit Hcov. unfold covered in Hcov. apply Exists_exists in Hcov as (c & Hin & Hic).
  pose proof (proj1 (forallb_forall _ _) H c Hin) as Hc. cbn beta in Hc.
  pose proof (proj1 (Forall_forall _ _) Hlit c Hin) as Hl. cbn beta in Hl.
  unfold in_cell in Hic. destruct (c_off c) as [o| | | | | | |]; try discriminate; try contradiction.
  rewrite soff_lit_small in Hic by lia. apply Bool.orb_true_iff in Hc as [Hc|Hc]; apply Z.leb_le in Hc; lia.
Qed.

Definition cells_lit62 (cells : list cell) : bool := ltac2:(tb__ "0|4|
S7bS16S16S15S34Lx;S1fR1A1S0S33S6SbS7Z2Z3eA2M0A1R1A2S6R1G0A2A2Lo;S1S37Li;S71S15S15S37Lb;La;M1Lop;M2G2S72G1Lop;M3G3S34S2S15S37La;Lw;Lsgn;S1S15S0S37Lk;Li;Ll;X15x8Lc;Vcells;A3").
Lemma cells_lit62_sound : ltac2:(tb__ "0|4|
S38S16A1S10S34S50R1A1S36A3S5aS16S16S15OLx;S1fR1A1S0SfS3SbS7Z2Z3eA2M0A1R1A2S3R1G0A2A2Lo;S1S12Li;S71S15S15S12Lb;La;M1Lop;M2G2S72G1Lop;M3G3S34S2S15S12La;Lw;Lsgn;S1S15S0S12Lk;Li;Ll;X15x8Lc;R2A3F_;Fcells;").
Proof using .
  intros cells H. apply Forall_forall. intros c Hin. pose proof (proj1 (forallb_forall _ _) H c Hin) as Hc. cbn beta in Hc.
  destruct (c_off c); try discriminate. apply andb_prop in Hc as [A B]. apply Z.leb_le in A. apply Z.leb_le in B. lia.
Qed.

Lemma held_image_untouched : ltac2:(tb__ "0|4|
S18S5dS43Q40A1S35S43Q8A1A1M0F_;S17S0S0S0S0S1eVsegs;R8R7R5A4S10S15S1bR6A1S19Z0M1A1A3S10S15S24R7A1S19R4A1M2A3S10S15S23R8A1G2A3S10S2aS29R9A1S2dA3S10S34S4fS1cRaA1R9R8A3S36A3S10S34S50S1cRbA1A1S36A3S3G1R9A2S3RaRcA2S3S4RdRcA2RaA2S5RbS7Z2Z3eA2A2S0SfS3R10R1A2S5R1S4R10RfA2A2A2S10G0R13S60R2A1M3A1S5eR14G3A2A3F_;Fa;S47R12R10RfA3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fwhi;Fwlo;Fn;Flo;Fo;Fm;Fms;Frho;").
Proof using .
  intros rho ms m o lo n wlo whi Hoh Hb Hlo Hhi Hd Hcl Hlit H0 H1 H2 H3 Hm a Ha.
  rewrite (Hm a Ha). destruct Hoh as (_ & _ & _ & Hdf & _).
  unfold obj_lo_of, obj_hi_of in Hdf. rewrite Hb, Hlo, Hhi, Hd in Hdf. cbn [eval] in Hdf.
  replace (bv_unsigned (Z_to_bv 64 0)) with 0 in Hdf by reflexivity. rewrite !soff_lit_small in Hdf by lia.
  specialize (Hdf a ltac:(lia) (cells_clear_sound rho _ lo n a Hcl Ha (cells_lit62_sound _ Hlit))).
  cbn [dflt_holds] in Hdf. rewrite Z.add_0_l in Hdf. exact (proj1 Hdf).
Qed.

Definition rom_bytes_ok (a : Z) (bs : list byte) : bool := ltac2:(tb__ "0|3|
S7bS3bS3bS33S2cVsegs;S45Q40S4Va;S9R1A1A2A2M0A2S35S43Q8M1A1M2A1S34Lx;S28Vsegs;G0A2G2SeS44G1R1A2S44G1S5bG2R2Vbs;S45G1Z0A2A4A2A2Lb;S37X35x2A2Lk;S5cU0S3fG2Vbs;A2A2A3").

Lemma rom_bytes_ok_sound : ltac2:(tb__ "0|4|
S0S38S43Q8M0A1M1A1S10S34S59R2R1A2S36A3S0SfS3Z0M2R1A2S5R1S9S3fG1R3A2A1A2A2SfS10S34S2cVsegs;S45Q40S4R5R2A2A2M3A2S36A3S10S35G1A1S28Vsegs;G3A2S3aG1S5bG1SaR2A1R4S45G0G2A2A4A2A3A2F_;Fk;F_;Fbs;Fa;").
Proof using .
  intros a bs H k Hk. unfold rom_bytes_ok in H.
  pose proof (proj1 (forallb_forall _ _) H (Z.to_nat k) ltac:(apply in_seq; lia)) as X. cbn beta in X.
  rewrite Z2Nat.id in X by lia. apply andb_prop in X as [X1 X2]. split; [exact X1|].
  destruct (image_byte segs (Z_to_bv 64 (a + k))) as [b|]; [|discriminate]. apply Z.eqb_eq in X2. f_equal. apply bv_eq. exact X2.
Qed.

End P.
