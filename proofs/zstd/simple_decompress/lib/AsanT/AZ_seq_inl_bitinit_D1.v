From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_seq_kit AZ_seq_gkit AZ_seq_d_base AZ_seq_d_lbase AZ_seq_d_lkit AZ_seq_d_akit AZ_seq_d_okit AZ_seq_d_ibase AZ_seq_d_iat AZ_seq_d_ikit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac kxa_norm ::= unfold shspan in *.
Ltac kxl_hyp ::= lazymatch goal with |- ?G => first [ match goal with H : G |- _ => exact H end | match goal with H : rheld G |- _ => exact H end ] end.
Ltac kxa_rng ::= first [ kxl_hyp | kxa_rng0 ].
Ltac kxl_rng ::=
  first [ kxl_hyp
        | lazymatch goal with |- rng ?RNG ?A ?N => match goal with H : rng RNG ?A0 ?N0 |- _ => apply (rng_sub' RNG A0 N0 A N H); solve [kxl_lia_small] end end
        | kx_rng ].
Tactic Notation "kx_autoFLA_v" constr(VMAX) constr(CH) uconstr(AKS) uconstr(STOPS) constr(FUEL) uconstr(KZS) uconstr(RRS) uconstr(WWS) :=
  let stops := constr:(STOPS : list Z) in let aks := constr:(AKS : list kza) in let kzs := constr:(KZS : list kz) in
  let rrs := constr:(RRS : list (Z * Z)) in let wws := constr:(WWS : list (Z * Z)) in
  kx_autoFLA_core (VMAX : Z) stops (FUEL : nat) true CH aks kzs rrs wws.
Ltac bid_enum :=
  let BCE := fresh "BCE" in
  match goal with
  | BDC : rw_cells _ _ ?B _ |- _ =>
    is_var B;
    lazymatch type of BDC with
    | context [C4 (Z_to_bv 64 (-1 * Z.lxor (bv_unsigned (edenot ?E ?e)) 31 + ?c))] =>
        kx_read_ranges;
        lazymatch e with context [EVar ?j] =>
          kx_enum BCE E e j 1 255%nat (fun v => (1 <=? (-1 * Z.lxor v 31 + c) mod 2^64) && ((-1 * Z.lxor v 31 + c) mod 2^64 <=? 8))%bool end
    | context [C4 (Z_to_bv 64 (bv_unsigned (edenot ?E ?e) + ?c))] =>
        kx_read_ranges;
        lazymatch e with context [EVar ?j] =>
          kx_enum BCE E e j 1 255%nat (fun v => (1 <=? (v + c) mod 2^64) && ((v + c) mod 2^64 <=? 64))%bool end
    | context [C4 (Z_to_bv 64 (bv_unsigned (edenot ?E ?e)))] =>
        kx_read_ranges;
        lazymatch e with context [EVar ?j] =>
          kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v mod 2^64) && (v mod 2^64 <=? 64))%bool end
    | context [C4 (edenot ?E ?e)] =>
        kx_read_ranges;
        lazymatch e with context [EVar ?j] =>
          kx_enum BCE E e j 1 255%nat (fun v => (1 <=? v mod 2^64) && (v mod 2^64 <=? 64))%bool end
    end;
    cbv beta in BCE; apply andb_prop in BCE; destruct BCE as [BCE1 BCE2]; apply Z.leb_le in BCE1, BCE2
  end.
Ltac bid_ix cs off :=
  let rec go k :=
    let ok := eval vm_compute in (Nat.leb k (length cs)) in
    lazymatch ok with
    | true =>
        let b := eval vm_compute in (Z.eqb (Z.of_nat (cells_size (firstn k cs))) off) in
        lazymatch b with true => k | false => go (S k) end
    end in
  go O.
Ltac bid_merge H lo hi :=
  lazymatch type of H with rw_cells _ _ _ ?cs =>
    let a := bid_ix cs lo in let b := bid_ix cs hi in sqd_blob_seg H a b end.
Ltac bid_walk_n FR FRF PT SEQ FRB FF SPV DCTX LLT n :=
  kx_autoFLA_v 8 (FR, FRF, PT) [KAApp FRB 216; KAApp FF 256; KAUnp SEQ n; KAUnp DCTX 8; KAUnp (LLT + 4) 4] [0x93498; 0x94744] 300%nat
    [KZRange SPV 4704 (2^47); KZRange FRB 17594333495296 (2^47 - 320); KZRange FF 6443008 (2^47 - 576); KZAlign SPV 16; KZAlign FRB 32; KZAlign FF 256;
     KZRange SEQ 4096 (2^47 - 2); KZRange (SEQ + n) 4097 (2^47 - 1); KZRange n 8 (2^47 - 4096);
     KZRange DCTX 4096 (2^47 - 95992); KZAlign DCTX 8; KZRange LLT 4096 (2^47 - 4104); KZAlign LLT 8; KZImg 0x21754 0x2176c;
     KZWr FRB 216; KZWr FF 256; KZDisj FF 256 FRB 216; KZDisj FRB 216 SEQ n; KZDisj FF 256 SEQ n; KZDisj FRB 216 DCTX 95992; KZDisj FF 256 DCTX 95992]
    [(SEQ, n); (FRB, 216); (FF, 256)]
    [(FRB, 216); (FF, 256)].
Ltac bid_walk_c FR FRF PT SEQ FRB FF SPV DCTX LLT NN :=
  kx_autoFLA_v 8 (FR, FRF, PT) [KAApp FRB 216; KAApp FF 256; KAUnp SEQ NN; KAUnp DCTX 8; KAUnp (LLT + 4) 4] [0x93498; 0x94744] 300%nat
    [KZRange SPV 4704 (2^47); KZRange FRB 17594333495296 (2^47 - 320); KZRange FF 6443008 (2^47 - 576); KZAlign SPV 16; KZAlign FRB 32; KZAlign FF 256;
     KZRange SEQ 4096 (2^47 - 2); KZRange (SEQ + NN) 4097 (2^47 - 1);
     KZRange DCTX 4096 (2^47 - 95992); KZAlign DCTX 8; KZRange LLT 4096 (2^47 - 4104); KZAlign LLT 8; KZImg 0x21754 0x2176c;
     KZWr FRB 216; KZWr FF 256; KZDisj FF 256 FRB 216; KZDisj FRB 216 SEQ NN; KZDisj FF 256 SEQ NN; KZDisj FRB 216 DCTX 95992; KZDisj FF 256 DCTX 95992]
    [(SEQ, NN); (FRB, 216); (FF, 256)]
    [(FRB, 216); (FF, 256)].
Ltac bid_side RDSEQ SQB RAI :=
  try (lazymatch goal with |- (_ /\ _ /\ _) /\ rd_at _ _ _ _ => split; [repeat split; lia | exact RDSEQ] end);
  try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]);
  try kx_acc RAI;
  try sqd_aclose;
  try kx_mem.
Ltac bid_ok CONT TRANS FF :=
  bid_enum;
  match goal with HF : rw_cells _ ?mc FF ?cs |- _ =>
    lazymatch cs with
    | context [C4 (Z_to_bv 64 ?v)] =>
        eapply (CONT mc _ _ _ _ _ _ _ _ _ _ (v mod 2^64));
        [ eapply TRANS; [assumption | assumption | assumption | eassumption | rewrite KXS.Z_to_bv64_mod; exact HF]
        | lia
        | unfold bit_ok; intros _; first [left; lia | right; lia] ]
    | context [C4 (edenot ?E ?e)] =>
        eapply (CONT mc _ _ _ _ _ _ _ _ _ _ (bv_unsigned (edenot E e) mod 2^64));
        [ eapply TRANS; [assumption | assumption | assumption | eassumption | rewrite KXS.Z_to_bv64_mod, Z_to_bv_bv_unsigned; exact HF]
        | lia
        | unfold bit_ok; intros _; first [left; lia | right; lia] ]
    end
  end.
Ltac bid_err IERR TRANS FRB FF :=
  match goal with HR : rw_cells _ ?mc FRB _, HF : rw_cells _ ?mc FF _ |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
    bid_merge HR 96 216; bid_merge HR 64 88; bid_merge HR 0 56; bid_merge HF 0 248;
    eapply IERR; eapply TRANS; [assumption | assumption | assumption | exact HR | exact HF]
  end.
Ltac bid_leaf CONT TRANS IERR FRB FF :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x93498) _ _ _ _) => bid_ok CONT TRANS FF
  | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x94744) _ _ _ _) => bid_err IERR TRANS FRB FF
  end.

Section CANSEC1. Context {rc : runConstT}.

Definition sq_inl_bitinit_D1_stmt : Prop :=
  forall P OEND LLO LEND LOCV, sqd_static P OEND LLO LEND LOCV ->
  ai_I1 P OEND LLO LEND LOCV -> sqd_at_ierr P OEND LLO LEND LOCV -> ai_I0 P OEND LLO LEND LOCV.

Theorem sq_inl_bitinit_D1_proof : sq_inl_bitinit_D1_stmt.
Proof.
  unfold sq_inl_bitinit_D1_stmt. intros P OEND LLO LEND LOCV ST CONT IERR.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbv delta [ai_I0 sqd_ifrA sqd_iffA]. cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1].
  intros m1 ja jb jc jbd j72 p0 p1 p2 T72 T80 T88 T104 T192 A4 x1 x10 x11 x12 INV E72 E80 E88 E104 E192 EA4.
  subst T72 T80 T88 T104 T192 A4.
  cbv delta [ai_I1 sqd_iregsB sqd_ifrB sqd_iffB] in CONT. cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in CONT.
  unfold sqd_at_ierr in IERR. cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in IERR.
  pose proof (sqd_iinv_frame _ _ _ _ _ _ _ _ ST INV) as TRANS. cbn [w_FRB w_FF] in TRANS.
  pose proof (sqd_itbl_asan _ _ _ _ _ _ _ _ ST INV) as (ALL & _ & _). cbn [w_RNG w_LLT w_tLL] in ALL.
  pose proof (sqd_itbl_logs _ _ _ _ _ _ _ _ ST INV) as (_ & _ & _ & TLB & _ & _). cbn [w_tLL] in TLB.
  apply (sqd_iopen_k _ _ _ _ _ _ _ _ ST INV); cbn [w_FRB w_FF w_DCTX w_LLT w_MLT w_OFT w_huf w_SEQ w_sq w_RNG]; intros FR FRF PT SQB MI UFF USEQ RSQ RSQS UD RD RDS.
  apply (sqd_rg_k _ _ _ _ _ ST); cbn [w_FRB w_FF w_SPV w_lo w_RNG w_SHF]; intros RGA1 RGA2 RGA3 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RSTK RFF RSHF RGC1 RGC2.
  pose proof ST as ST0. sd_static_open ST. unfold held in RGB.
  cbn [sqd_astat] in S61. destruct S61 as (AST & _ & _ & _ & ED8 & _). destruct AST as (_ & _ & RAI).
  remember (map (Z_to_bv 8) sq) as sqb eqn:Esqb. remember (zlen sq) as n eqn:En.
  try rewrite <- En in USEQ. try rewrite <- En in RSQ. try rewrite <- En in RSQS.
  unfold DCTX_SIZEOF in UD, RD, RDS. unfold dctx_ptrs in PT.
  assert (DJF : FF + 256 <= SEQ \/ SEQ + n <= FF) by (unfold held in S56; clear - S56 En; lia).
  assert (DJR : FRB + 216 <= SEQ \/ SEQ + n <= FRB) by (unfold held in S25; clear - S25 S18 S47 En; lia).
  assert (DJD1 : FRB + 216 <= DCTX \/ DCTX + 95992 <= FRB) by (unfold held in S27; clear - S27 S18 S47; lia).
  assert (DJD2 : FF + 256 <= DCTX \/ DCTX + 95992 <= FF) by (unfold held in S54; clear - S54; lia).
  assert (RGN : 1 <= n /\ 4096 <= SEQ /\ SEQ + n < 2^47) by (clear - S13 S14 S15 En; subst n; lia).
  assert (RGD : 4096 <= DCTX /\ DCTX + 95992 < 2^47 /\ DCTX mod 8 = 0 /\ 4096 <= LLT /\ LLT + 4104 <= 2^47 /\ LLT mod 8 = 0 /\ FF mod 256 = 0 /\ FRB mod 32 = 0)
    by (clear - S19 S20 S21 S44 S51 S48 ED8; lia).
  assert (ALT : aro RNG m1 LLT 16).
  { apply (aro_sub _ _ _ _ _ _ ALL); [lia | lia |]. pose proof (Z.pow_pos_nonneg 2 (st_log tLL) ltac:(lia) ltac:(lia)). lia. }
  destruct ALT as (ULT & RLT & RLTS). clear ALL UFF.
  assert (MUL : munch [(FRB, FRB + 216); (FF, FF + 256)] m1 m1) by apply munch_refl.
  assert (WMl : wmono bsegs m1 m1) by apply wmono_refl.
  destruct RGN as (RN1 & RN2 & RN3). destruct RGD as (RD1 & RD2 & RD3 & RD4 & RD5 & RD6 & RD7 & RD8).
  assert (RSP : 4704 <= SPV < 2^47) by (clear - S17; lia).
  assert (RFB : 17594333495296 <= FRB /\ FRB + 320 <= 2^47) by (clear - RGA7 S47 S17; lia).
  assert (RFF2 : 6443008 <= FF /\ FF + 576 <= 2^47) by (clear - RGA2 S50 S18 S17; lia).
  assert (RDSEQ : rd_at bsegs m1 SEQ n).
  { pose proof (rd_at_bytes_at _ _ _ _ SQB) as HR. subst. rewrite length_map in HR. exact HR. }
  hold CONT. hold IERR. hold TRANS. hold INV. hold ST0. hold En. hold Esqb. hold TLB.
  hold S1. hold S2. hold S3. hold S4. hold S5. hold S6. hold S7. hold S8. hold S9. hold S10. hold S11. hold S12. hold S13. hold S14. hold S15. hold S16. hold S17. hold S18. hold S19. hold S20.
  hold S21. hold S22. hold S23. hold S24. hold S25. hold S26. hold S27. hold S28. hold S29. hold S30. hold S31. hold S32. hold S33. hold S34. hold S35. hold S36. hold S37. hold S38. hold S39. hold S40.
  hold S41. hold S42. hold S43. hold S44. hold S45. hold S46. hold S47. hold S48. hold S49. hold S50. hold S51. hold S52. hold S53. hold S54. hold S55. hold S56. hold S57. hold S58. hold S59. hold S60.
  try hold S62. try hold S63. try hold S64. try hold S65. try hold S66. try hold S67. try hold S68. try hold S69. try hold OKLL. try hold OKOF. try hold OKML.
  assert (NC : 8 <= n \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7) by lia.
  destruct NC as [N8|[N|[N|[N|[N|[N|[N|N]]]]]]].
  - bid_walk_n FR FRF PT SEQ FRB FF SPV DCTX LLT n.
    all: try clear DJF DJR DJD1 DJD2. all: bid_side RDSEQ SQB RAI. all: try unfold held in CONT, TRANS, IERR, En.
    all: bid_leaf CONT TRANS IERR FRB FF.
  - subst n. bid_walk_c FR FRF PT SEQ FRB FF SPV DCTX LLT 1.
    all: try clear DJF DJR DJD1 DJD2. all: bid_side RDSEQ SQB RAI. all: try unfold held in CONT, TRANS, IERR, En.
    all: bid_leaf CONT TRANS IERR FRB FF.
  - subst n. bid_walk_c FR FRF PT SEQ FRB FF SPV DCTX LLT 2.
    all: try clear DJF DJR DJD1 DJD2. all: bid_side RDSEQ SQB RAI. all: try unfold held in CONT, TRANS, IERR, En.
    all: bid_leaf CONT TRANS IERR FRB FF.
  - subst n. bid_walk_c FR FRF PT SEQ FRB FF SPV DCTX LLT 3.
    all: try clear DJF DJR DJD1 DJD2. all: bid_side RDSEQ SQB RAI. all: try unfold held in CONT, TRANS, IERR, En.
    all: bid_leaf CONT TRANS IERR FRB FF.
  - subst n. bid_walk_c FR FRF PT SEQ FRB FF SPV DCTX LLT 4.
    all: try clear DJF DJR DJD1 DJD2. all: bid_side RDSEQ SQB RAI. all: try unfold held in CONT, TRANS, IERR, En.
    all: bid_leaf CONT TRANS IERR FRB FF.
  - subst n. bid_walk_c FR FRF PT SEQ FRB FF SPV DCTX LLT 5.
    all: try clear DJF DJR DJD1 DJD2. all: bid_side RDSEQ SQB RAI. all: try unfold held in CONT, TRANS, IERR, En.
    all: bid_leaf CONT TRANS IERR FRB FF.
  - subst n. bid_walk_c FR FRF PT SEQ FRB FF SPV DCTX LLT 6.
    all: try clear DJF DJR DJD1 DJD2. all: bid_side RDSEQ SQB RAI. all: try unfold held in CONT, TRANS, IERR, En.
    all: bid_leaf CONT TRANS IERR FRB FF.
  - subst n. bid_walk_c FR FRF PT SEQ FRB FF SPV DCTX LLT 7.
    all: try clear DJF DJR DJD1 DJD2. all: bid_side RDSEQ SQB RAI. all: try unfold held in CONT, TRANS, IERR, En.
    all: bid_leaf CONT TRANS IERR FRB FF.
Qed.

End CANSEC1.
