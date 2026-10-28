(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim MuslStrlen MemcpyLib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_memcpy_base U_code_43000_43c04.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
#[local] Existing Instance PropExec.fx0.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_P_memchr () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Lib.PropExec.v_and"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.v_or"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.v_sub"; "stdpp.bitvector.definitions.Z_to_bv"; "Mc"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.v_xor"; "Hc"; "stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "Stdlib.ZArith.BinInt.Z.testbit"; "TW"; "Corelib.Init.Datatypes.andb"; "Corelib.Init.Datatypes.negb"; "RocqVerifyHarness.AgentSubmission.BB.MuslStrlen.HZ.Tz"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Peano.lt"; "Corelib.Init.Logic.not"; "Corelib.Lists.ListDef.nth"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.c_eq"; "LDv"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Datatypes.option"; "rodata_clear"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.bytes_le_to_Z"; "Corelib.Init.Peano.le"; "Corelib.Init.Nat.add"; "RocqVerifyHarness.AgentSubmission.BB.MemcpyLib.sub"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.BB.Hoare.at_"; "MCHR.sb_"; "MCHR.b_"; "Stdlib.ZArith.BinInt.Z.lt"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.BB.Hoare.ret_ok"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.msteps"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "RocqVerifyHarness.AgentSubmission.BB.MemcpyLib.keeps_cs"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.v_andi"; "mchrH"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition Mc : Z := 0x0101010101010100.   (* [comment removed for export] *)
Definition Hc : Z := 0x8080808080808080.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition LDv (l : list byte) : word := Z_to_bv 64 (bytes_le_to_Z l).

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L36773063779.3L53386175970.300000800@S1l1H2H0S1l1H2H0". (* [comment removed for export] *)
Lemma u_LDv : forall l, length l = 8%nat -> bv_unsigned (LDv l) = bytes_le_to_Z l.
Proof. intros l H. unfold LDv. pose proof (bytes_le_to_Z_range l H). apply u_Z2bv; lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Definition TW (x : word) : word := ltac2:(CDefT.buildp (gd_tbl_P_memchr ()) "(0.(1.(2.(3.&40.$4.)(5.O1.(3.&40.=)))(5.O1.(3.&40.=)))(3.&40.$6.))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L15043813962.1L38955485601.1000001002SS". (* [comment removed for export] *)
Lemma v_xor_0 : forall x : word, v_xor x (Z_to_bv 64 0) = x.
Proof.
  intros x. unfold v_xor. rewrite (u_Z2bv 0) by lia. rewrite Z.lxor_0_r. apply Z_to_bv_bv_unsigned.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00G0?L10351595562.7 L11601612111.8 L11601617044.7 L11603594827.3 L11608664069.4 L11978622192.3 L15759366616.8 L19456177677.10L19837313665.6 L19841481962.10L23902351436.7 L27051992771.7 L27343556470.8 L35497642998.10L36260862899.7 L38944120794.6 L38948407713.2 L38954701265.5 L38960193291.10L41231917500.7 L4832158337.6  L53214546604.8 L8929562017.7  00000:00C00H00K00P00S00a00k01001501?01G01S01X01a01f01g01l02902>02C02H02PS1x1A1i2HiS1x1z1q1rS1x1AS1xS1x1zS1xS1x2Hx1z1q1r1HS1x1A1i2HhS1x1AS1x1AS1x1A1i2HiS1x2Hx1AS1x1z1q1r2H0S1x1AS1x1A3A64S1x1ASS1x1zS1x1A1i2Hi2HlS1x1AS1x1AS1x1AS1x1A2R1". (* [comment removed for export] *)
Lemma TW_bits : ltac2:(CDefT.buildp (gd_tbl_P_memchr ()) "Px,(7.&40.)Zy,$8.(9.&40.R1.)(:.Pi,$8.P,(;.=R1.)(<.$=.(>.(9.&40.(?.R4.))R2.)(10.(>.$6.R2.)(11.(>.(12.R3.)R2.))))Pi,$8.P,(;.=R1.)P,(<.$=.(>.(12.R3.)R2.)$13.)(<.$=.(>.$6.R3.)$13.))")
(* [comment removed for export] *).
Proof.
  intros x y. pose proof (u64_range x) as Hx. subst y.
  assert (A64 : (0 <= (bv_unsigned x + HZ.ONESNEG) mod 2 ^ 64 < 2 ^ 64)%Z) by (apply Z.mod_pos_bound; lia).
  set (A := ((bv_unsigned x + HZ.ONESNEG) mod 2 ^ 64)%Z) in *.
  (* [comment removed for export] *)
  assert (SUB : ((Mc - bv_unsigned x) mod 2 ^ 64 = 2 ^ 64 - 1 - A)%Z).
  { subst A. unfold Mc, HZ.ONESNEG.
    rewrite <- (Z.mod_add _ 1) by lia.
    replace (72340172838076672 - bv_unsigned x + 1 * 2 ^ 64)%Z
      with (2 ^ 64 - 1 - (bv_unsigned x + 18374403900871474943) + 1 * 2 ^ 64)%Z by lia.
    set (z := (bv_unsigned x + 18374403900871474943)%Z).
    rewrite Zminus_mod_idemp_r || idtac.
    pose proof (Z.div_mod z (2^64) ltac:(lia)). pose proof (Z.mod_pos_bound z (2^64) ltac:(lia)).
    set (q := (z / 2 ^ 64)%Z) in *. set (r := (z mod 2 ^ 64)%Z) in *.
    replace (2 ^ 64 - 1 - z + 1 * 2 ^ 64)%Z with ((2 ^ 64 - 1 - r) + (1 - q) * 2 ^ 64)%Z by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (NOTA : forall i, (0 <= i < 64)%Z -> Z.testbit (2 ^ 64 - 1 - A) i = negb (Z.testbit A i)).
  { intros i Hi. replace (2 ^ 64 - 1 - A)%Z with ((Z.lnot A) mod 2 ^ 64)%Z.
    - rewrite Z.mod_pow2_bits_low by lia. apply Z.lnot_spec. lia.
    - unfold Z.lnot. replace (Z.pred (- A)) with ((2 ^ 64 - 1 - A) + (-1) * 2 ^ 64)%Z by lia.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (TWu : bv_unsigned (TW x) = Z.land (Z.lor ((Mc - bv_unsigned x) mod 2 ^ 64) (bv_unsigned x)) Hc).
  { unfold TW. rewrite !v_xor_0. unfold v_and, v_or, v_sub.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
    rewrite (Z.mod_small Mc) by (unfold Mc; lia). rewrite (Z.mod_small Hc) by (unfold Hc; lia).
    assert (R1 : (0 <= (Mc - bv_unsigned x) mod 2 ^ 64 < 2 ^ 64)%Z) by (apply Z.mod_pos_bound; lia).
    assert (R2 : (0 <= Z.lor ((Mc - bv_unsigned x) mod 2 ^ 64) (bv_unsigned x) < 2 ^ 64)%Z) by (apply Z_lor_range; lia).
    rewrite (Z.mod_small (Z.lor _ _)) by exact R2.
    apply Z.mod_small. apply Z_land_range; [exact R2 | unfold Hc; lia]. }
  split.
  - intros i Hi. rewrite TWu, SUB.
    unfold HZ.Tz. fold A.
    rewrite Z.land_spec. rewrite Z.lor_spec. rewrite Z.land_spec. rewrite Z.land_spec. rewrite Z.lxor_spec.
    change HZ.HIGHS with Hc.
    destruct (Z.lt_ge_cases i 64) as [Hl|Hh].
    + rewrite NOTA by lia.
      replace (Z.testbit HZ.ALLONES i) with true.
      2:{ symmetry. unfold HZ.ALLONES. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.ones_spec_low; [reflexivity|lia]. }
      destruct (Z.testbit A i), (Z.testbit (bv_unsigned x) i), (Z.testbit Hc i); reflexivity.
    + replace (Z.testbit Hc i) with false.
      2:{ symmetry. apply (Z_testbit_high 64); unfold Hc; lia. }
      rewrite andb_false_r. reflexivity.
  - intros i Hi H. unfold HZ.Tz in H. rewrite Z.land_spec in H. rewrite Z.land_spec in H.
    change HZ.HIGHS with Hc in H.
    destruct (Z.testbit Hc i); [reflexivity|]. rewrite andb_false_r in H. discriminate H.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L10351595562.7L3714546647.3 L53214284460.3000006007008S1i2HiSS". (* [comment removed for export] *)
Lemma TW_eq_H : forall x : word, c_eq (TW x) (Z_to_bv 64 Hc) = Z.eqb (HZ.Tz (bv_unsigned x)) 0.
Proof.
  intros x. destruct (TW_bits x) as [B1 B2].
  unfold c_eq, bv_eqb. rewrite (u_Z2bv Hc) by (unfold Hc; lia).
  pose proof (HZ.Tz_range (bv_unsigned x)) as TR.
  destruct (Z.eqb_spec (HZ.Tz (bv_unsigned x)) 0) as [Z0|NZ].
  - apply Z.eqb_eq. apply Z.bits_inj'. intros i Hi. rewrite B1 by lia. rewrite Z0, Z.bits_0.
    rewrite andb_true_r. reflexivity.
  - apply Z.eqb_neq. intros E.
    apply NZ. apply Z.bits_inj'. intros i Hi. rewrite Z.bits_0.
    destruct (Z.testbit (HZ.Tz (bv_unsigned x)) i) eqn:T; [|reflexivity].
    pose proof (B2 i Hi T) as HH.
    pose proof (B1 i Hi) as BB. rewrite E, HH, T in BB. discriminate BB.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma TW_nozero : ltac2:(CDefT.buildp (gd_tbl_P_memchr ()) "Pl,(14.(7.&8.))P,(<.$15.(16.(7.&8.)R1.)#8.)P,Pi,$15.P,(17.R1.#8.)(18.(<.$8.(9.&8.(19.(7.&8.)R2.R4.(3.&8.=)))=))(<.$=.(1:.(?.(1;.R3.))(3.&40.$6.))$13.)")
(* [comment removed for export] *).
Proof.
  intros l Hl Hnz. rewrite TW_eq_H. apply Z.eqb_eq.
  rewrite u_LDv by exact Hl. apply HZ.Tz_nozero.
  - apply bytes_le_to_Z_range. exact Hl.
  - intros i Hi. rewrite zb_of_bytes by (rewrite Hl; exact Hi). apply Hnz. exact Hi.
Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L62340516925.800000@S1l1i2Hl2Hi1j2Hj". (* [comment removed for export] *)
Lemma TW_haszero : ltac2:(CDefT.buildp (gd_tbl_P_memchr ()) "Pl,(14.(7.&8.))Pi,$15.P,(<.$15.(16.(7.&8.)R2.)#8.)P,(17.R2.#8.)P,(<.$8.(9.&8.(19.(7.&8.)R3.R4.(3.&8.=)))=)P,Pj,$15.P,(17.R1.R5.)(18.(<.$8.(9.&8.(19.(7.&8.)R2.R7.(3.&8.=)))=))(<.$=.(1:.(?.(1;.R6.))(3.&40.$6.))$1<.)")
(* [comment removed for export] *).
Proof.
  intros l i Hl Hi Hz Hnz. rewrite TW_eq_H. apply Z.eqb_neq.
  rewrite u_LDv by exact Hl. apply (HZ.Tz_haszero _ i).
  - apply bytes_le_to_Z_range. exact Hl.
  - exact Hi.
  - rewrite zb_of_bytes by (rewrite Hl; exact Hi). exact Hz.
  - intros j Hj. rewrite zb_of_bytes by (rewrite Hl; lia). apply Hnz. exact Hj.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rodata_clear (mem : word -> option byte) : Prop :=
  forall i, (0x10c30 <= i < 0x10c58)%Z -> mem (Z_to_bv 64 i) = None.

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L19814693217.4L32153182839.2000006007S1x2HxS". (* [comment removed for export] *)
Lemma rd_const_M : ltac2:(CDefT.buildp (gd_tbl_P_memchr ()) "Pmem,P,(7.&40.)(1=.(7.&8.))P,(1>.R1.)(1?.(14.(7.&8.))Lbs,(14.(7.&8.))(:.(<.(1=.(14.(7.&8.)))(20.$21.R3.(3.&40.+10<48.)#8.)(22.(14.(7.&8.))R1.))(<.$8.(23.R1.)(9.&40.(3.&40.$4.)))))")
(* [comment removed for export] *).
Proof.
  intros mem Hr.
  rewrite (rdn_ext RSEGS 8 mem (fun _ => None)).
  - eexists. split; [vm_compute; reflexivity|]. vm_compute. reflexivity.
  - change (bv_unsigned (Z_to_bv 64 68680)) with 68680%Z. cbn. lia.
  - intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hr.
    change (bv_unsigned (Z_to_bv 64 68680)) with 68680%Z in Hx. cbn in Hx. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L19814693217.4L26705053431.2000006007S1x2HxS". (* [comment removed for export] *)
Lemma rd_const_H : ltac2:(CDefT.buildp (gd_tbl_P_memchr ()) "Pmem,P,(7.&40.)(1=.(7.&8.))P,(1>.R1.)(1?.(14.(7.&8.))Lbs,(14.(7.&8.))(:.(<.(1=.(14.(7.&8.)))(20.$21.R3.(3.&40.+10<30.)#8.)(22.(14.(7.&8.))R1.))(<.$8.(23.R1.)(9.&40.(3.&40.$6.)))))")
(* [comment removed for export] *).
Proof.
  intros mem Hr.
  rewrite (rdn_ext RSEGS 8 mem (fun _ => None)).
  - eexists. split; [vm_compute; reflexivity|]. vm_compute. reflexivity.
  - change (bv_unsigned (Z_to_bv 64 68656)) with 68656%Z. cbn. lia.
  - intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hr.
    change (bv_unsigned (Z_to_bv 64 68656)) with 68656%Z in Hx. cbn in Hx. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nth_sub : ltac2:(CDefT.buildp (gd_tbl_P_memchr ()) "Pbs,(14.(7.&8.))Pj,$15.Pm,$15.Pi,$15.Pd,(7.&8.)P,(17.R2.R3.)P,(24.(25.R5.R4.)(16.(7.&8.)R6.))(<.(7.&8.)(19.(7.&8.)R4.(26.(7.&8.)R7.R6.R5.)R3.)(19.(7.&8.)(25.R6.R4.)R7.R3.))")
(* [comment removed for export] *).
Proof.
  intros bs j m i d Hi Hjm. unfold sub.
  rewrite nth_firstn. replace (i <? m)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi).
  rewrite nth_skipn. reflexivity.
Qed.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L15043196704.2L27842253743.2L38955064523.2L60096197530.200000100600700<SS1b1RSS1b1R". (* [comment removed for export] *)
Lemma c_eq_LBv_0 : forall b : byte, c_eq (LBv b) (Z_to_bv 64 0) = (bv_unsigned b =? 0)%Z.
Proof.
  intros b. unfold c_eq, bv_eqb, LBv. pose proof (bv_unsigned_in_range _ b) as R.
  change (bv_modulus 8) with 256%Z in R.
  rewrite (u_Z2bv (bv_unsigned b)) by lia. rewrite (u_Z2bv 0) by lia. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record mchrH (mem : word -> option byte) (s : word) (buf : list byte) (K n : Z) : Prop := MCHRH {
  (* [comment removed for export] *)
  Hbuf : rdn RSEGS mem s (length buf) = Some buf;
  (* [comment removed for export] *)
  Hwin : ((bv_unsigned s + K) / 8 * 8 + 8 <= bv_unsigned s + Z.of_nat (length buf))%Z;
  Hnw  : (bv_unsigned s + Z.of_nat (length buf) < 2 ^ 64)%Z;
  (* [comment removed for export] *)
  HK0  : (0 <= K)%Z;
  Hzero : bv_unsigned (nth (Z.to_nat K) buf (Z_to_bv 8 0)) = 0%Z;
  Hnz  : forall j, (j < Z.to_nat K)%nat -> bv_unsigned (nth j buf (Z_to_bv 8 0)) <> 0%Z;
  (* [comment removed for export] *)
  HKn  : (K + 8 <= n)%Z;
  Hn64 : (n < 2 ^ 64)%Z;
  Hro  : rodata_clear mem }.

Section MCHR.
  Variable mem : word -> option byte.
  Variable s : word.
  Variable buf : list byte.
  Variables K n : Z.
  Variable rom : word -> option byte.
  Hypothesis HOK : mchrH mem s buf K n.

  #[local] Notation L := (Z.of_nat (length buf)).
  Definition b_ (j : Z) : byte := nth (Z.to_nat j) buf (Z_to_bv 8 0).
  Definition sb_ (j : Z) (m : nat) : list byte := sub buf (Z.to_nat j) m.

  Let Hbuf := Hbuf _ _ _ _ _ HOK.
  Let Hwin : ((bv_unsigned s + K) / 8 * 8 + 8 <= bv_unsigned s + L)%Z := Hwin _ _ _ _ _ HOK.
  Let Hnw : (bv_unsigned s + L < 2 ^ 64)%Z := Hnw _ _ _ _ _ HOK.
  Let HK0 : (0 <= K)%Z := HK0 _ _ _ _ _ HOK.
  Let HKn : (K + 8 <= n)%Z := HKn _ _ _ _ _ HOK.
  Let Hn64 : (n < 2 ^ 64)%Z := Hn64 _ _ _ _ _ HOK.
  Let Hro := Hro _ _ _ _ _ HOK.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L34588993469.11L61035084364.9 L63368316718.1000000F00O00XS1s3buf1K4Hwin1H2H02H1S1s3buf1KS1s3buf1K". (* [comment removed for export] *)
  #[using="mem s n HOK Hwin"] Lemma KL : (K + 1 <= L)%Z.
  Proof.
    clear -Hwin HK0. pose proof (u64_range s).
    pose proof (Z.div_mod (bv_unsigned s + K) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (bv_unsigned s + K) 8 ltac:(lia)). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition KE : Z := ((bv_unsigned s + K) / 8 * 8 + 8 - bv_unsigned s)%Z.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L15352904086.11L15515372885.11L22662615766.11L39678177588.11L4408167912.11 L61028780023.11L61035084364.9 L63368316718.1000000E00F00T00]00l01501>01GS1s3buf1K3HK01H2H02H1FS1s3buf1K4HwinS1s3buf1KS1s3buf1K2H02H1S1s3buf1KS1s3buf1KS1s3buf1K". (* [comment removed for export] *)
  #[using="mem n HOK Hwin HK0"] Lemma KE_facts : (K + 1 <= KE <= K + 8)%Z /\ (KE <= L)%Z /\ ((bv_unsigned s + KE) mod 8 = 0)%Z.
  Proof.
    unfold KE. clear -Hwin HK0. pose proof (u64_range s).
    pose proof (Z.div_mod (bv_unsigned s + K) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (bv_unsigned s + K) 8 ltac:(lia)).
    repeat split; try lia.
    replace (bv_unsigned s + ((bv_unsigned s + K) / 8 * 8 + 8 - bv_unsigned s))%Z
      with (8 + ((bv_unsigned s + K) / 8) * 8)%Z by lia.
    rewrite Z.mod_add by lia. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="mem s n HOK"] Lemma bz : bv_unsigned (b_ K) = 0%Z.
  Proof. exact (Hzero _ _ _ _ _ HOK). Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L5552348055.1600000>S1s3buf1K1j2Hj". (* [comment removed for export] *)
  #[using="mem s n HOK"] Lemma bnz : forall j, (0 <= j < K)%Z -> bv_unsigned (b_ j) <> 0%Z.
  Proof. intros j Hj. unfold b_. apply (Hnz _ _ _ _ _ HOK). lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L12055101381.18L27022714613.1800000C00SS1s3buf1K1j1m2Hj2HmS1s3buf1K1j1m2Hj". (* [comment removed for export] *)
  #[using="K n HOK Hbuf"] Lemma rd_w : ltac2:(CDefT.buildp (gd_tbl_P_memchr ()) "Pj,$8.Pm,$15.P,(;.=R2.)P,(;.(27.R3.(28.R2.))(28.(16.(7.&8.)Vbuf,)))(<.(1=.(14.(7.&8.)))(20.$21.Vmem,(29.Vs,R4.)R3.)(22.(14.(7.&8.))(2:.R4.R3.)))")
(* [comment removed for export] *).
  Proof.
    intros j m Hj Hm. unfold sb_.
    replace (at_ s j) with (at_ s (Z.of_nat (Z.to_nat j))) by (f_equal; lia).
    apply (rdn_sub RSEGS mem (length buf)); [exact Hbuf | lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L21622188601.17L45272746471.17L61160209964.1700000>00L00]S1s3buf1K1j2H1S1s3buf1K1j2HjS1s3buf1K1j2Hj2H1". (* [comment removed for export] *)
  #[using="K n HOK Hbuf"] Lemma rd_b : forall j, (0 <= j)%Z -> (j + 1 <= L)%Z ->
    rdn RSEGS mem (at_ s j) 1 = Some [b_ j].
  Proof.
    intros j Hj H1. rewrite (rd_w j 1) by lia. unfold sb_, b_.
    rewrite sub_nth; [reflexivity | lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L12055101381.1800000CS1s3buf1K1j1m2Hj2Hm". (* [comment removed for export] *)
  #[using="s K"] Lemma sb_len : forall j m, (0 <= j)%Z -> (j + Z.of_nat m <= L)%Z -> length (sb_ j m) = m.
  Proof. intros j m Hj Hm. unfold sb_. apply sub_length. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L10093989218.19L24117499887.19L67337960637.1900000>00T00gS1s3buf1K1i2HiS1s3buf1K1j1i2Hj2Hi2H8S1s3buf1K1j1i2Hj2Hi". (* [comment removed for export] *)
  #[using="s K"] Lemma sb_nth : ltac2:(CDefT.buildp (gd_tbl_P_memchr ()) "Pj,$8.Pi,$15.P,(;.=R2.)P,(17.R2.#8.)P,(;.(27.R4.+8.)(28.(16.(7.&8.)Vbuf,)))(<.(7.&8.)(19.(7.&8.)R4.(2:.R5.#8.)(3.&8.=))(2;.(27.R5.(28.R4.))))")
(* [comment removed for export] *).
  Proof.
    intros j i Hj Hi H8. unfold sb_, b_. rewrite nth_sub by lia. f_equal. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L18009872776.29L45270656359.2900000?00NS1s3buf1K1j3Hj1S1s3buf1K1j3Hj0". (* [comment removed for export] *)
  #[using="K n HOK Hbuf"] Lemma m_lbu : forall regs pc w rd rs (imm : bv 12) j0 j,
    fetch_word RSEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
    getr regs rs = at_ s j0 -> (j0 + bv_signed imm = j)%Z ->
    (0 <= j)%Z -> (j + 1 <= L)%Z ->
    RiscvSemantics.step RSEGS (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LBv (b_ j))) (v_addi pc 4) mem rom).
  Proof.
    intros regs pc w rd rs imm j0 j Hf He Hd Hrs Hj Hj0 Hj1.
    eapply step_lbu; [exact Hf | exact He | exact Hd |].
    rewrite Hrs, at_addi, Hj. apply rd_b; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L21624276658.29L45270656364.2900000?00NS1s3buf1K1j3Hj8S1s3buf1K1j3Hj0". (* [comment removed for export] *)
  #[using="K n HOK Hbuf"] Lemma m_ld : forall regs pc w rd rs (imm : bv 12) j0 j,
    fetch_word RSEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load SZ8 true rd rs imm, 4%Z) ->
    getr regs rs = at_ s j0 -> (j0 + bv_signed imm = j)%Z ->
    (0 <= j)%Z -> (j + 8 <= L)%Z ->
    RiscvSemantics.step RSEGS (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LDv (sb_ j 8))) (v_addi pc 4) mem rom).
  Proof.
    intros regs pc w rd rs imm j0 j Hf He Hd Hrs Hj Hj0 Hj8.
    eapply step_ld; [exact Hf | exact He | exact Hd | |].
    - rewrite Hrs, at_addi, Hj. apply (rd_w j 8); lia.
    - symmetry. apply u_LDv. apply sb_len; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L12435766423.14L61028780023.13L61035084364.11L61699331511.15L63368316460.14L63368316718.1200000:00A00F00c00j011S1s1K1j2HjS1s1K1jS1s1jS1s1K3HK01j3Hal2Hj1H2H02H12H2S1s1K1jS1s1K1j". (* [comment removed for export] *)
  #[using="mem buf n HOK HK0"] Lemma al_room : forall j, ((bv_unsigned s + j) mod 8 = 0)%Z -> (0 <= j <= K)%Z -> (j + 8 <= KE)%Z.
  Proof.
    intros j Hal Hj. unfold KE. clear -Hal Hj HK0. pose proof (u64_range s).
    pose proof (Z.div_mod (bv_unsigned s + K) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (bv_unsigned s + K) 8 ltac:(lia)).
    pose proof (Z.div_mod (bv_unsigned s + j) 8 ltac:(lia)).
    assert ((bv_unsigned s + j) / 8 <= (bv_unsigned s + K) / 8)%Z by (apply Z.div_le_mono; lia).
    lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L18350927478.18L21622183302.18L27011960231.18L27014061761.20L45270656318.20L45272757848.18L48575855450.20L57251495599.18L63154211901.2000000>00L00Z00o01D01R01g02602LS1s3buf1K1j2HjS1s3buf1K1j2HLS1s3buf1K1j2HLS1s3buf1K1j2HL2jj3HjjS1s3buf1K1j2Hj2jj3HjjS1s3buf1K1j2HjS1s3buf1K1j2Hj2jj3HjjS1s3buf1K1j3HKjS1s3buf1K1j3HKj2jj3Hjj". (* [comment removed for export] *)
  #[using="mem s n HOK"] Lemma tw_hit : ltac2:(CDefT.buildp (gd_tbl_P_memchr ()) "Pj,$8.P,(:.(;.=R1.)(;.R1.VK,))P,(2<.VK,(27.R2.+8.))P,(;.(27.R3.+8.)(28.(16.(7.&8.)Vbuf,)))(<.$=.(1:.(?.(1;.(2:.R4.#8.)))(3.&40.$6.))$1<.)")
(* [comment removed for export] *).
  Proof.
    intros j Hj HKj HL.
    apply (TW_haszero _ (Z.to_nat (K - j))).
    - apply sb_len; lia.
    - lia.
    - rewrite sb_nth by lia. rewrite <- bz. f_equal. unfold b_. f_equal. lia.
    - intros jj Hjj. rewrite sb_nth by lia. apply bnz. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L10093995185.20L21622183302.18L27011964480.20L45272753599.20L45272757848.18L48577952731.2000000>00L00_01201@01WS1s3buf1K1i2HiS1s3buf1K1j2HLS1s3buf1K1j2HL1i2HiS1s3buf1K1j2Hj1i2HiS1s3buf1K1j2HjS1s3buf1K1j2Hj3HKj1i2Hi". (* [comment removed for export] *)
  #[using="mem s n HOK"] Lemma tw_miss : ltac2:(CDefT.buildp (gd_tbl_P_memchr ()) "Pj,$8.P,(;.=R1.)P,(;.(27.R2.+8.)VK,)P,(;.(27.R3.+8.)(28.(16.(7.&8.)Vbuf,)))(<.$=.(1:.(?.(1;.(2:.R4.#8.)))(3.&40.$6.))$13.)")
(* [comment removed for export] *).
  Proof.
    intros j Hj HKj HL. apply TW_nozero.
    - apply sb_len; lia.
    - intros i Hi. rewrite sb_nth by lia. apply bnz. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply m_lbu with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | f_equal; lia] | imm_norm; lia | lia | lia]
      | step_simpl]; vnorm.
  Ltac mld F D jj :=
    chain_step; [reflexivity
      | eapply m_ld with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | f_equal; lia] | imm_norm; lia | lia | lia]
      | step_simpl]; vnorm.

  (* [comment removed for export] *)
  Ltac condb :=
    rwH; rewrite c_eq_LBv_0;
    first [ apply Z.eqb_eq; rewrite <- bz; f_equal; f_equal; lia
          | apply Z.eqb_neq; apply bnz; lia ].
  (* [comment removed for export] *)
  Ltac cond := try unfold v_addi; cond_lia.
  (* [comment removed for export] *)
  Ltac condw lem :=
    rwH;
    lazymatch goal with |- c_eq (v_and (v_or (v_sub _ (v_xor ?x _)) _) _) _ = ?b =>
      change (c_eq (TW x) (Z_to_bv 64 Hc) = b) end;
    apply lem; lia.

  Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try reflexivity; try (f_equal; lia);
               try (unfold v_addi; unorm; f_equal; lia); try solve_keeps_cs.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L33805615823.21L34591087110.21L49629191847.21L66748616.21   00000900D00Q00RS1s3buf1KS1s3buf1K1HS1s3buf1K3HK0F". (* [comment removed for export] *)
  #[using="buf n HOK Hbuf Hwin HK0"] Lemma t_found : ltac2:(CDefT.buildp (gd_tbl_P_memchr ()) "Pregs,(2=.&5.(7.&40.))Pret,(7.&40.)P,(2>.R1.)P,(<.(7.&40.)(2?.R3.(30.&5.+1.$31.))R2.)P,(<.(7.&40.)(2?.R4.(30.&5.+:.$31.))(29.Vs,VK,))P,(<.(7.&40.)(2?.R5.(30.&5.+;.$31.))(3.&40.=))(1?.(2=.&5.(7.&40.))Lregs',(2=.&5.(7.&40.))(:.(32.$21.(33.$34.R7.(30.&40.+469>4.$31.)Vmem,Vrom,)(33.$34.R1.R6.Vmem,Vrom,))(:.(<.(7.&40.)(2?.R1.(30.&5.+:.$31.))(29.Vs,VK,))(35.R7.R1.))))")
(* [comment removed for export] *).
  Proof.
    intros regs ret Hret H1 H10 H11. pose proof KL. eexists. split.
    - mlbu F_43298 D_43298 K.                       (* [comment removed for export] *)
      stepb_tk F_4329c D_4329c ltac:(condb).        (* [comment removed for export] *)
      stepret F_432b0 D_432b0 ret ltac:(exact H1).
      apply mst_refl.
    - post.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00L0?L12201022352.27L13598069645.27L13598069645.29L15045126621.27L15045126621.29L21488483749.35L21488527567.29L23234619671.27L23234619671.29L24939385160.29L27695502712.29L3319138038.35 L34121046318.35L34588985825.27L34761421337.29L36226663266.27L36226663266.29L37309641873.29L38594852545.27L38948405814.27L38948405814.29L4428434371.27 L4428434371.29 L49631284544.27L52987091516.27L52987091516.29L5304342027.27 L5304342027.29 00000A00T00i01701G01Z01m01n01o02?02R02b03703I03]04004E04F04W04e05505H05]05o06B06W06j07?S1s3buf1K1j2Hj2HiS1s3buf1K1j1m2Hi2HmS1s3buf1K1i1j1m2Hi2HmS1s3buf1K1j2HiS1s3buf1K1i1j2HiS1s3buf1K1i1j2Hj2HiS1s3buf1K1i1j2Hj2HiFFS1s3buf1K1i1j2HiS1s3buf1K1i1j2Hj2HiS1s3buf1K1i1j2HiS1s3buf1K1i1j1m2Hi2HmS1s3buf1K3HKL1j2HiS1s3buf1K3HKL1i1j2HiS1s3buf1K1j1m2Hi2HmS1s3buf1K1i1j1m2Hi2HmFS1s3buf1K1j2Hj2HiS1s3buf1K1j2HiS1s3buf1K1i1j2HiS1s3buf1K1j1m2Hi2HmS1s3buf1K1i1j1m2Hi2HmS1s3buf1K3HK01j2HiS1s3buf1K1j1m2Hi2HmS1s3buf1K1i1j1m2Hi2HmS1s3buf1K1j1m2Hi2HmS1s3buf1K1i1j1m2Hi2Hm". (* [comment removed for export] *)
  #[using="buf n HOK Hbuf Hwin HK0"] Lemma t_loop : ltac2:(CDefT.buildp (gd_tbl_P_memchr ()) "Pi,$15.Pregs,(2=.&5.(7.&40.))Pret,(7.&40.)Pj,$8.Pm,$8.P,(2>.R3.)P,(<.(7.&40.)(2?.R5.(30.&5.+1.$31.))R4.)P,(<.(7.&40.)(2?.R6.(30.&5.+:.$31.))(29.Vs,R4.))P,(<.(7.&40.)(2?.R7.(30.&5.+;.$31.))(3.&40.=))P,(<.(7.&40.)(2?.R8.(30.&5.+=.$31.))(3.&40.R5.))P,(:.(;.=R7.)(2<.R7.VK,))P,(<.$8.(28.R;.)(36.(36.VK,+1.)R8.))P,(:.(;.(27.(36.VK,R9.)+1.)R8.)(2<.R8.(37.+2.+40.)))(1?.(2=.&5.(7.&40.))Lregs',(2=.&5.(7.&40.))(:.(32.$21.(33.$34.R=.(30.&40.+469><.$31.)Vmem,Vrom,)(33.$34.R1.R<.Vmem,Vrom,))(:.(<.(7.&40.)(2?.R1.(30.&5.+:.$31.))(29.Vs,VK,))(35.R=.R1.))))")
(* [comment removed for export] *).
  Proof.
    pose proof KL as HKL.
    induction i as [|i IH]; intros regs ret j m Hret H1 H10 H11 H13 Hj Hi Hm.
    - (* [comment removed for export] *)
      eexists. split.
      + stepn F_432a0 D_432a0.                      (* [comment removed for export] *)
        stepn F_432a4 D_432a4.                      (* [comment removed for export] *)
        stepb_tk F_432a8 D_432a8 ltac:(cond).       (* [comment removed for export] *)
        mlbu F_43298 D_43298 K.                     (* [comment removed for export] *)
        stepb_tk F_4329c D_4329c ltac:(condb).      (* [comment removed for export] *)
        stepret F_432b0 D_432b0 ret ltac:(exact H1).
        apply mst_refl.
      + post.
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x469ec : word) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = at_ s (j + 1) /\ getr r 11 = Z_to_bv 64 0
                         /\ getr r 13 = Z_to_bv 64 (m - 1) /\ keeps_cs regs r)).
      + eexists. split.
        * stepn F_432a0 D_432a0.                    (* [comment removed for export] *)
          stepn F_432a4 D_432a4.                    (* [comment removed for export] *)
          stepb_tk F_432a8 D_432a8 ltac:(cond).     (* [comment removed for export] *)
          mlbu F_43298 D_43298 (j + 1)%Z.           (* [comment removed for export] *)
          stepb_ft F_4329c D_4329c ltac:(condb).    (* [comment removed for export] *)
          apply mst_refl.
        * post.
      + cbv beta. (intros r1 dd_H; ddestruct dd_H as (R1 & R10 & R11 & R13 & KC)).
        ddestruct (IH r1 ret (j + 1)%Z (m - 1)%Z Hret R1 R10 R11 R13 ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & A10 & K2).
        exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00S0?L11093370175.39L12121121174.39L15091237842.44L18009872822.38L2139732837.49 L22276887954.38L23232523253.38L23283027868.6 L23285129889.38L27014057281.39L27014061734.38L36228764263.39L44644949641.39L45197731806.49L45270656345.38L45270660798.39L5180349044.7  L5182448814.39 L52331444932.39L5302241038.39 L55043946905.38L55045991953.44L60428660524.38L60428664011.39L60762847550.39L61028779636.7 L61028789167.4 L61028789167.5 L61030889646.5 L63368316589.8 L63374621462.5 L63374621462.6 L65470775786.39L66832947188.39L67186183030.4400000@00\00o01H01_02402502B02T03903W04304H04]04n05A05P05d06406I06^07307A07Q07R07\07d07n08808B08J08T09009109FS1s3buf1K1i1j2HiS1s3buf1K1i1j1m2Hj2Hi2Hm3HKjS1s3buf1K1j1m2Hi2HmS1s3buf1K4HKE21j2Hj2Hi2HRS1s3buf1K1i1j2Hj2Hi3HKjS1s3buf1K1j2Hj2Hi3HjKFS1K1j2Hi1H2H0S1s3buf1K1j2Hi3HKjS1s3buf1K3HKL4HKE14HKE21i1j2Hj2Hi3HKjS1s3buf1K4Hwin4HKE21j2Hj2Hi2HRS1s3buf1K1i1j1m2Hj2Hi2Hm3HKjS1s3buf1K1i1j1m2Hi2HmS1s3buf1K1i1j1m2Hi2HmS1s3buf1K1j2Hj2HiS1s3buf1K1i1j2Hj2HiS1K1i1j2Hj2Hi1HS1s3buf1K1i1j2Hi3HKjS1s3buf1K1i1j2HiS1s3buf1K1i1j1m2Hi2HmS1s3buf1K1j2Hj2Hi3HjKS1s3buf1K1j2Hj2Hi3HjKS1s3buf1K1j2HiS1s3buf1K1i1j2HiFS1K1i1j2HiS1K1j2HiS1K1i1j2HiS1K1i1j2HiS1K1i1j2HiS1K1j2HiS1K1i1j2HiS1s3buf1K1i1j1m2Hj2Hi2Hm3HKjFS1s3buf1K1j2Hj2Hi3HjK". (* [comment removed for export] *)
  #[using="buf n HOK Hbuf Hwin HK0"] Lemma w_loop : ltac2:(CDefT.buildp (gd_tbl_P_memchr ()) "Pi,$15.Pregs,(2=.&5.(7.&40.))Pret,(7.&40.)Pj,$8.Pm,$8.P,(2>.R3.)P,(<.(7.&40.)(2?.R5.(30.&5.+1.$31.))R4.)P,(<.(7.&40.)(2?.R6.(30.&5.+:.$31.))(29.Vs,R4.))P,(<.(7.&40.)(2?.R7.(30.&5.+;.$31.))(3.&40.=))P,(<.(7.&40.)(2?.R8.(30.&5.+<.$31.))(3.&40.R5.))P,(<.(7.&40.)(2?.R9.(30.&5.+=.$31.))(3.&40.$4.))P,(<.(7.&40.)(2?.R:.(30.&5.+>.$31.))(3.&40.$6.))P,(<.(7.&40.)(2?.R;.(30.&5.+?.$31.))(3.&40.=))P,(<.(7.&40.)(2?.R<.(30.&5.+10.$31.))(3.&40.+7.))P,(:.(;.=R;.)(;.R;.VK,))P,(<.$8.(38.(27.(9.&40.Vs,)R<.)+8.)=)P,(<.$8.(28.R10.)(39.(36.VK,R=.)+8.))P,(:.(;.(27.(36.VK,R>.)+8.)R=.)(2<.R=.(37.+2.+40.)))(1?.(2=.&5.(7.&40.))Lregs',(2=.&5.(7.&40.))(:.(32.$21.(33.$34.R12.(30.&40.+469;8.$31.)Vmem,Vrom,)(33.$34.R1.R11.Vmem,Vrom,))(:.(<.(7.&40.)(2?.R1.(30.&5.+:.$31.))(29.Vs,VK,))(35.R12.R1.))))")
(* [comment removed for export] *).
  Proof.
    pose proof KL as HKL. dpose KE_facts as (HKE1 & HKE2 & HKE3).
    induction i as [|i IH]; intros regs ret j m Hret H1 H10 H11 H12 H13 H14 H15 H16 Hj Hal Hi Hm;
      pose proof (al_room j Hal Hj) as HR.
    - (* [comment removed for export] *)
      assert (HKj : (K < j + 8)%Z).
      { clear -Hi Hj. pose proof (Z.div_mod (K - j) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (K - j) 8 ltac:(lia)). lia. }
      destruct (Z.eq_dec j K) as [HjK|HjK].
      + (* [comment removed for export] *)
        eexists. split.
        * mld F_4326c D_4326c j.                    (* [comment removed for export] *)
          stepn F_43270 D_43270.                    (* [comment removed for export] *)
          stepn F_43274 D_43274.                    (* [comment removed for export] *)
          stepn F_43278 D_43278.                    (* [comment removed for export] *)
          stepn F_4327c D_4327c.                    (* [comment removed for export] *)
          stepb_tk F_43280 D_43280 ltac:(condw tw_hit).   (* [comment removed for export] *)
          stepn F_432b4 D_432b4.                    (* [comment removed for export] *)
          mlbu F_432b8 D_432b8 j.                   (* [comment removed for export] *)
          stepb_ft F_432bc D_432bc ltac:(condb).    (* [comment removed for export] *)
          stepn F_432c0 D_432c0.                    (* [comment removed for export] *)
          stepret F_432b0 D_432b0 ret ltac:(exact H1).
          apply mst_refl.
        * post.
      + (* [comment removed for export] *)
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x469ec : word) mem rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = at_ s j /\ getr r 11 = Z_to_bv 64 0
                           /\ getr r 13 = Z_to_bv 64 m /\ keeps_cs regs r)).
        * eexists. split.
          -- mld F_4326c D_4326c j.
             stepn F_43270 D_43270.
             stepn F_43274 D_43274.
             stepn F_43278 D_43278.
             stepn F_4327c D_4327c.
             stepb_tk F_43280 D_43280 ltac:(condw tw_hit).
             stepn F_432b4 D_432b4.                 (* [comment removed for export] *)
             mlbu F_432b8 D_432b8 j.                (* [comment removed for export] *)
             stepb_tk F_432bc D_432bc ltac:(condb). (* [comment removed for export] *)
             apply mst_refl.
          -- post.
        * cbv beta. (intros r1 dd_H; ddestruct dd_H as (R1 & R10 & R11 & R13 & KC)).
          ddestruct (t_loop (Z.to_nat (K - 1 - j)) r1 ret j m Hret R1 R10 R11 R13
                      ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & A10 & K2).
          exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
    - (* [comment removed for export] *)
      assert (HKj : (j + 8 <= K)%Z).
      { clear -Hi Hj. pose proof (Z.div_mod (K - j) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (K - j) 8 ltac:(lia)). lia. }
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x469b8 : word) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = at_ s (j + 8) /\ getr r 11 = Z_to_bv 64 0
                         /\ getr r 12 = Z_to_bv 64 (m - 8) /\ getr r 13 = Z_to_bv 64 Mc /\ getr r 14 = Z_to_bv 64 Hc
                         /\ getr r 15 = Z_to_bv 64 0 /\ getr r 16 = Z_to_bv 64 7 /\ keeps_cs regs r)).
      + eexists. split.
        * mld F_4326c D_4326c j.
          stepn F_43270 D_43270.
          stepn F_43274 D_43274.
          stepn F_43278 D_43278.
          stepn F_4327c D_4327c.
          stepb_ft F_43280 D_43280 ltac:(condw tw_miss).  (* [comment removed for export] *)
          stepn F_43284 D_43284.                    (* [comment removed for export] *)
          stepn F_43288 D_43288.                    (* [comment removed for export] *)
          stepb_tk F_4328c D_4328c ltac:(cond).     (* [comment removed for export] *)
          apply mst_refl.
        * post.
      + cbv beta. (intros r1 dd_H; ddestruct dd_H as (R1 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & KC)).
        ddestruct (IH r1 ret (j + 8)%Z (m - 8)%Z Hret R1 R10 R11 R12 R13 R14 R15 R16 ltac:(lia)
                    ltac:(rewrite Z.add_assoc, <- Zplus_mod_idemp_l, Hal; reflexivity)
                    ltac:(clear -Hi HKj; pose proof (Z.div_mod (K - j) 8 ltac:(lia));
                          pose proof (Z.mod_pos_bound (K - j) 8 ltac:(lia));
                          pose proof (Z.div_mod (K - (j + 8)) 8 ltac:(lia));
                          pose proof (Z.mod_pos_bound (K - (j + 8)) 8 ltac:(lia)); nia)
                    ltac:(lia)) as (r2 & RUN & A10 & K2).
        exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac ldc F D vv RD :=
    chain_step; [reflexivity
      | eapply step_ld with (v := vv);
        [exact F | reflexivity | exact D
        | gres; imm_norm;
          lazymatch goal with |- rdn _ _ ?a _ = _ =>
            lazymatch type of RD with rdn _ _ ?c _ = _ =>
              replace a with c by (apply bv_eq; vm_compute; reflexivity) end end;
          exact RD
        | assumption ]
      | step_simpl]; vnorm.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00C0?L11583828408.39L15047224127.39L18009872822.39L21098353503.4 L22276887954.39L33535680872.39L36228759936.39L38950502612.39L42866253887.39L44349634750.39L44611056089.39L45270656345.39L45637567181.39L48785726404.39L5302244585.39 L55043946905.39L60428660524.39L63370422803.39L6753814915.39 00000;00F00Y00a01301>01]01h01i02=02H02V02W03203B03T03_03j045S1s3buf1K1jS1s3buf1K1jS1s3buf1K1j4HKE22HRS1K1j2HjS1s3buf1K1j2Hj3HjKS1s3buf1K1jS1s3buf1K1j1m2Hm3HjK2Hj4HKE12HRS1s3buf1K1jFS1s3buf1K1j1m2Hm3HjKS1s3buf1K1jS1s3buf1K1j2HjFS1s3buf1K1j1m2Hj2Hm4HKE12HRS1s3buf1K1j1m2HmS1s3buf1K1j2Hj3HjKS1s3buf1K1jS1s3buf1K1jS1s3buf1K1j". (* [comment removed for export] *)
  #[using="buf n HOK Hbuf Hwin HK0 Hro"] Lemma a_entry : ltac2:(CDefT.buildp (gd_tbl_P_memchr ()) "Pregs,(2=.&5.(7.&40.))Pret,(7.&40.)Pj,$8.Pm,$8.P,(2>.R3.)P,(<.(7.&40.)(2?.R5.(30.&5.+1.$31.))R4.)P,(<.(7.&40.)(2?.R6.(30.&5.+:.$31.))(29.Vs,R4.))P,(<.(7.&40.)(2?.R7.(30.&5.+;.$31.))(3.&40.=))P,(<.(7.&40.)(2?.R8.(30.&5.+<.$31.))(3.&40.R5.))P,(<.(7.&40.)(2?.R9.(30.&5.+>.$31.))(3.&40.+1.))P,(:.(;.=R8.)(;.R8.VK,))P,(<.$8.(38.(27.(9.&40.Vs,)R9.)+8.)=)P,(:.(;.(27.(36.VK,R:.)+8.)R9.)(2<.R9.(37.+2.+40.)))(1?.(2=.&5.(7.&40.))Lregs',(2=.&5.(7.&40.))(:.(32.$21.(33.$34.R>.(30.&40.+46988.$31.)Vmem,Vrom,)(33.$34.R1.R=.Vmem,Vrom,))(:.(<.(7.&40.)(2?.R1.(30.&5.+:.$31.))(29.Vs,VK,))(35.R>.R1.))))")
(* [comment removed for export] *).
  Proof.
    intros regs ret j m Hret H1 H10 H11 H12 H14 Hj Hal Hm.
    pose proof KL as HKL. dpose KE_facts as (HKE1 & HKE2 & HKE3). pose proof (al_room j Hal Hj) as HR.
    ddestruct (rd_const_M mem Hro) as (bsM & RM & EM).
    ddestruct (rd_const_H mem Hro) as (bsH & RH & EH).
    destruct (Z.eq_dec j K) as [HjK|HjK].
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x469e4 : word) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = at_ s K /\ getr r 11 = Z_to_bv 64 0 /\ keeps_cs regs r)).
      + eexists. split.
        * stepb_ft F_4323c D_4323c ltac:(cond).     (* [comment removed for export] *)
          mlbu F_43240 D_43240 j.                   (* [comment removed for export] *)
          stepb_tk F_43244 D_43244 ltac:(condb).    (* [comment removed for export] *)
          stepn F_43290 D_43290.                    (* [comment removed for export] *)
          stepb_ft F_43294 D_43294 ltac:(cond).     (* [comment removed for export] *)
          apply mst_refl.
        * post.
      + cbv beta. (intros r1 dd_H; ddestruct dd_H as (R1 & R10 & R11 & KC)).
        ddestruct (t_found r1 ret Hret R1 R10 R11) as (r2 & RUN & A10 & K2).
        exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x469b8 : word) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = at_ s j /\ getr r 11 = Z_to_bv 64 0
                         /\ getr r 12 = Z_to_bv 64 m /\ getr r 13 = Z_to_bv 64 Mc /\ getr r 14 = Z_to_bv 64 Hc
                         /\ getr r 15 = Z_to_bv 64 0 /\ getr r 16 = Z_to_bv 64 7 /\ keeps_cs regs r)).
      + eexists. split.
        * stepb_ft F_4323c D_4323c ltac:(cond).     (* [comment removed for export] *)
          mlbu F_43240 D_43240 j.                   (* [comment removed for export] *)
          stepb_ft F_43244 D_43244 ltac:(condb).    (* [comment removed for export] *)
          stepn F_43248 D_43248.                    (* [comment removed for export] *)
          stepb_ft F_4324c D_4324c ltac:(cond).     (* [comment removed for export] *)
          stepn F_43250 D_43250.                    (* [comment removed for export] *)
          ldc F_43254 D_43254 (Z_to_bv 64 Mc) RM.   (* [comment removed for export] *)
          stepn F_43258 D_43258.                    (* [comment removed for export] *)
          ldc F_4325c D_4325c (Z_to_bv 64 Hc) RH.   (* [comment removed for export] *)
          stepn F_43260 D_43260.                    (* [comment removed for export] *)
          stepiv F_43264 D_43264 (Z_to_bv 64 0)
            ltac:(gres; rwH; apply bv_eq; vm_compute; reflexivity).   (* [comment removed for export] *)
          vnorm.
          stepn F_43268 D_43268.                    (* [comment removed for export] *)
          apply mst_refl.
        * post.
      + cbv beta. (intros r1 dd_H; ddestruct dd_H as (R1 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & KC)).
        ddestruct (w_loop (Z.to_nat ((K - j) / 8)) r1 ret j m Hret R1 R10 R11 R12 R13 R14 R15 R16 Hj Hal
                    ltac:(clear -Hj; pose proof (Z.div_pos (K - j) 8); lia) Hm) as (r2 & RUN & A10 & K2).
        exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac snez1 :=
    match goal with |- context [v_sltu ?a ?b] =>
      replace (v_sltu a b) with (Z_to_bv 64 1)
        by (symmetry; rwH; unfold v_sltu; rewrite c_ltu_ltb; try unfold v_addi; unorm;
            rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity) end.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L24982522600.16L29784461188.16L65806776729.16L66813785540.1600000900B00P00^S1s3buf1KS1s3buf1KS1s3buf1K1j2HjS1s3buf1K1j2Hj". (* [comment removed for export] *)
  #[using="buf K"] Lemma andi7_u : ltac2:(CDefT.buildp (gd_tbl_P_memchr ()) "Pj,$8.P,(:.(;.=(27.(9.&40.Vs,)R1.))(2<.(27.(9.&40.Vs,)R1.)(37.+2.+40.)))(<.$8.(9.&40.(3:.(29.Vs,R2.)+7.))(38.(27.(9.&40.Vs,)R2.)+8.))")
(* [comment removed for export] *).
  Proof.
    intros j Hj. rewrite u_andi by lia. rewrite at_u by lia.
    change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00_0?L11581727546.35L14090067294.38L14090067294.43L15045130685.35L15047224127.31L16423572877.31L18007771956.35L18009872822.31L18009872822.33L21488483749.38L21488483749.43L22276887954.31L22276887954.33L28337563730.43L33494134422.35L36226667266.35L36228759936.31L37309637873.35L37311739507.31L38948409942.35L38950502612.31L42866253887.31L42866253887.33L43294002699.35L43894746304.35L4426336545.31 L4428438435.35 L45270656345.31L45270656345.33L45272758235.35L52987087452.35L52989188318.31L5302244585.31 L5304338027.35 L55043946905.31L55046040347.35L60428660524.31L60428660524.33L60430761390.35L60671672259.8 L61339182115.38L61341266859.31L63368325877.7 L63370422803.33L6755916545.35 L8927109407.31 L8929211293.35 00000@00S00h01801F01G01j02H02`03503L03d04>04W05005H05^05_05`06006>06?06@06A06Y06o07G07X07k08>08S08f09909N09c0::0:H0:X0:h0;40;H0;\0;f0<60<F0<b0=@S1s3buf1K1i1j2HiS1s3buf1K1j1m2Hi2HmS1s3buf1K1i1j1m2Hi2HmS1s3buf1K1i1j2HiS1s3buf1K1j2HiFS1s3buf1K4Hwin3HK03HKL2Hs1i1j2Hj2HiS1s3buf1K3HKL1j2Hi3HjK4Hwin2HjS1s3buf1K3HKL1i1j2Hi3HjKS1s3buf1K1j2Hj2Hi3HjKS1s3buf1K1i1j2Hj2Hi3HjKS1s3buf1K2Hs1j2Hj2Hi3HjKS1s3buf1K2Hs1i1j2Hj2Hi3HjKS1s3buf1K2Hs1i1j2Hj2Hi2HMS1s3buf1K2Hs1i1j2Hj2Hi2HMS1s3buf1K1i1j1m2Hj2Hi2HmS1s3buf1K1j1m2Hj2Hi2HmFFS1s3buf1K1i1j2HiS1s3buf1K1j2HiFFFS1s3buf1K1i1j1m2Hj2Hi2HmS1s3buf1K1j1m2Hj2Hi2HmS1s3buf1K1i1j1m2Hj2Hi2HmS1s3buf1K1j2Hj2HiS1s3buf1K1i1j2Hj2HiS1s3buf1K1i1j2Hj2HiS1s3buf1K1i1j1m2Hi2HmS1s3buf1K1j1m2Hi2HmS1s3buf1K1j1m2Hi2HmS1s3buf1K1i1j1m2Hi2HmS1s3buf1K1j2Hj2Hi3HjKS1s3buf1K1i1j2Hj2Hi3HjKS1s3buf1K1j2HiS1s3buf1K1i1j2HiS1s3buf1K1i1j2HiS1s1i1j2Hi1HS1s3buf1K2Hs1j2Hj2HiS1s3buf1K2Hs1j2Hj2HiS1s1i1j2HiS1s3buf1K1i1j2HiS1s3buf1K1i1j2HiS1s3buf1K3Hnw3HKL2Hs1j2Hj2HiS1s3buf1K3Hnw3HKL2Hs1i1j2Hj2Hi". (* [comment removed for export] *)
  #[using="buf n HOK Hbuf Hwin Hnw HK0 Hro"] Lemma h_loop : ltac2:(CDefT.buildp (gd_tbl_P_memchr ()) "Pi,$15.Pregs,(2=.&5.(7.&40.))Pret,(7.&40.)Pj,$8.Pm,$8.P,(2>.R3.)P,(<.(7.&40.)(2?.R5.(30.&5.+1.$31.))R4.)P,(<.(7.&40.)(2?.R6.(30.&5.+:.$31.))(29.Vs,R4.))P,(<.(7.&40.)(2?.R7.(30.&5.+;.$31.))(3.&40.=))P,(<.(7.&40.)(2?.R8.(30.&5.+<.$31.))(3.&40.R5.))P,(<.(7.&40.)(2?.R9.(30.&5.+?.$31.))(29.Vs,(27.R7.+1.)))P,(<.(7.&40.)(2?.R:.(30.&5.+10.$31.))(3.&40.+1.))P,(:.(;.=R9.)(;.R9.VK,))P,(<.$8.(28.R=.)(36.+7.(38.(27.(9.&40.Vs,)R:.)+8.)))P,(:.(;.(27.(36.VK,R;.)+8.)R:.)(2<.R:.(37.+2.+40.)))(1?.(2=.&5.(7.&40.))Lregs',(2=.&5.(7.&40.))(:.(32.$21.(33.$34.R?.(30.&40.+46960.$31.)Vmem,Vrom,)(33.$34.R1.R>.Vmem,Vrom,))(:.(<.(7.&40.)(2?.R1.(30.&5.+:.$31.))(29.Vs,VK,))(35.R?.R1.))))")
(* [comment removed for export] *).
  Proof.
    pose proof KL as HKL. pose proof (u64_range s) as Hs.
    induction i as [|i IH]; intros regs ret j m Hret H1 H10 H11 H12 H15 H16 Hj Hi Hm.
    - (* [comment removed for export] *)
      destruct (Z.eq_dec j K) as [HjK|HjK].
      + eapply (runs_trans RSEGS _ (fun r => mkst r (0x469e4 : word) mem rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = at_ s K /\ getr r 11 = Z_to_bv 64 0 /\ keeps_cs regs r)).
        * eexists. split.
          -- mlbu F_43214 D_43214 j.                (* [comment removed for export] *)
             stepn F_43218 D_43218.                 (* [comment removed for export] *)
             stepb_tk F_4321c D_4321c ltac:(condb). (* [comment removed for export] *)
             apply mst_refl.
          -- post.
        * cbv beta. (intros r1 dd_H; ddestruct dd_H as (R1 & R10 & R11 & KC)).
          ddestruct (t_found r1 ret Hret R1 R10 R11) as (r2 & RUN & A10 & K2).
          exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
      + eapply (runs_trans RSEGS _ (fun r => mkst r (0x46988 : word) mem rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = at_ s (j + 1) /\ getr r 11 = Z_to_bv 64 0
                           /\ getr r 12 = Z_to_bv 64 (m - 1) /\ getr r 14 = Z_to_bv 64 1 /\ keeps_cs regs r)).
        * eexists. split.
          -- mlbu F_43214 D_43214 j.                (* [comment removed for export] *)
             stepn F_43218 D_43218.                 (* [comment removed for export] *)
             stepb_ft F_4321c D_4321c ltac:(condb). (* [comment removed for export] *)
             stepn F_43220 D_43220.                 (* [comment removed for export] *)
             stepn F_43224 D_43224.                 (* [comment removed for export] *)
             stepn F_43228 D_43228.                 (* [comment removed for export] *)
             stepn F_4322c D_4322c. snez1.          (* [comment removed for export] *)
             stepb_tk F_43230 D_43230
               ltac:(rwH; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_eq;
                     rewrite Z.add_assoc, <- Zplus_mod_idemp_l;
                     replace ((bv_unsigned s + j) mod 8)%Z with 7%Z by lia; reflexivity).  (* [comment removed for export] *)
             apply mst_refl.
          -- post.
        * cbv beta. (intros r1 dd_H; ddestruct dd_H as (R1 & R10 & R11 & R12 & R14 & KC)).
          ddestruct (a_entry r1 ret (j + 1)%Z (m - 1)%Z Hret R1 R10 R11 R12 R14 ltac:(lia)
                      ltac:(rewrite Z.add_assoc, <- Zplus_mod_idemp_l;
                            replace ((bv_unsigned s + j) mod 8)%Z with 7%Z by lia; reflexivity)
                      ltac:(lia)) as (r2 & RUN & A10 & K2).
          exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
    - (* [comment removed for export] *)
      destruct (Z.eq_dec j K) as [HjK|HjK].
      + eapply (runs_trans RSEGS _ (fun r => mkst r (0x469e4 : word) mem rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = at_ s K /\ getr r 11 = Z_to_bv 64 0 /\ keeps_cs regs r)).
        * eexists. split.
          -- mlbu F_43214 D_43214 j.
             stepn F_43218 D_43218.
             stepb_tk F_4321c D_4321c ltac:(condb).
             apply mst_refl.
          -- post.
        * cbv beta. (intros r1 dd_H; ddestruct dd_H as (R1 & R10 & R11 & KC)).
          ddestruct (t_found r1 ret Hret R1 R10 R11) as (r2 & RUN & A10 & K2).
          exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
      + pose proof (Z.mod_pos_bound (bv_unsigned s + j + 1) 8 ltac:(lia)) as HM1.
        assert (HM : ((bv_unsigned s + j + 1) mod 8 = (bv_unsigned s + j) mod 8 + 1)%Z).
        { clear -Hi Hs Hj. rewrite <- (Zplus_mod_idemp_l (bv_unsigned s + j)).
          pose proof (Z.mod_pos_bound (bv_unsigned s + j) 8 ltac:(lia)). apply Z.mod_small. lia. }
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x46960 : word) mem rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = at_ s (j + 1) /\ getr r 11 = Z_to_bv 64 0
                           /\ getr r 12 = Z_to_bv 64 (m - 1) /\ getr r 15 = at_ s (j + 1 + 1)
                           /\ getr r 16 = Z_to_bv 64 1 /\ keeps_cs regs r)).
        * eexists. split.
          -- mlbu F_43214 D_43214 j.                (* [comment removed for export] *)
             stepn F_43218 D_43218.                 (* [comment removed for export] *)
             stepb_ft F_4321c D_4321c ltac:(condb). (* [comment removed for export] *)
             stepn F_43220 D_43220.                 (* [comment removed for export] *)
             stepn F_43224 D_43224.                 (* [comment removed for export] *)
             stepn F_43228 D_43228.                 (* [comment removed for export] *)
             stepn F_4322c D_4322c. snez1.          (* [comment removed for export] *)
             stepb_ft F_43230 D_43230
               ltac:(rwH; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_neq;
                     rewrite Z.add_assoc; lia).     (* [comment removed for export] *)
             stepn F_43234 D_43234.                 (* [comment removed for export] *)
             stepb_tk F_43238 D_43238 ltac:(cond).  (* [comment removed for export] *)
             apply mst_refl.
          -- post.
        * cbv beta. (intros r1 dd_H; ddestruct dd_H as (R1 & R10 & R11 & R12 & R15 & R16 & KC)).
          ddestruct (IH r1 ret (j + 1)%Z (m - 1)%Z Hret R1 R10 R11 R12 R15 R16 ltac:(lia)
                      ltac:(rewrite Z.add_assoc; lia) ltac:(lia)) as (r2 & RUN & A10 & K2).
          exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00>0?L15047225310.25L15258988766.32L15258988766.33L16423571820.25L2427056828.25 L27196633914.25L38950503477.25L40207240895.25L48737112174.25L58925624865.32L58925624865.33L63368324587.23L63543401676.25L68272682437.3300000900M00a00b01801N01W01g02302@02M02V02W02fS1s3buf1KS1s3buf1K1n3HKn4Hn64S1s3buf1K1n3HKn4Hn64FS1s3buf1K1n3HK03HKn2HsS1s3buf1K1n3HK03HKn2HsS1s3buf1KS1s3buf1K1n4Hn64S1s3buf1K2HsS1s3buf1K3HK0S1s3buf1K3HK0S1s3buf1KFS1s3buf1K2Hs2HM". (* [comment removed for export] *)
  #[using="buf HOK Hbuf Hwin Hnw HK0 HKn Hn64 Hro"] Lemma memchr0_run : ltac2:(CDefT.buildp (gd_tbl_P_memchr ()) "Pregs,(2=.&5.(7.&40.))Pret,(7.&40.)P,(2>.R1.)P,(<.(7.&40.)(2?.R3.(30.&5.+1.$31.))R2.)P,(<.(7.&40.)(2?.R4.(30.&5.+:.$31.))Vs,)P,(<.(7.&40.)(2?.R5.(30.&5.+;.$31.))(3.&40.=))P,(<.(7.&40.)(2?.R6.(30.&5.+<.$31.))(3.&40.Vn,))(1?.(2=.&5.(7.&40.))Lregs',(2=.&5.(7.&40.))(:.(32.$21.(33.$34.R8.(30.&40.+46944.$31.)Vmem,Vrom,)(33.$34.R1.R7.Vmem,Vrom,))(:.(<.(7.&40.)(2?.R1.(30.&5.+:.$31.))(29.Vs,VK,))(35.R8.R1.))))")
(* [comment removed for export] *).
  Proof.
    intros regs ret Hret H1 H10 H11 H12.
    pose proof KL as HKL. pose proof (u64_range s) as Hs. rewrite <- (at_0 s) in H10.
    pose proof (Z.mod_pos_bound (bv_unsigned s) 8 ltac:(lia)) as HM.
    destruct (Z.eq_dec (bv_unsigned s mod 8) 0) as [Hal|Hal].
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x46988 : word) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = at_ s 0 /\ getr r 11 = Z_to_bv 64 0
                         /\ getr r 12 = Z_to_bv 64 n /\ getr r 14 = Z_to_bv 64 1 /\ keeps_cs regs r)).
      + eexists. split.
        * stepn F_431f8 D_431f8. rwH. vals_lit.     (* [comment removed for export] *)
          stepn F_431fc D_431fc.                    (* [comment removed for export] *)
          stepn F_43200 D_43200. snez1.             (* [comment removed for export] *)
          stepb_tk F_43204 D_43204
            ltac:(rwH; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_eq;
                  rewrite Z.add_0_r; exact Hal).    (* [comment removed for export] *)
          apply mst_refl.
        * post.
      + cbv beta. (intros r1 dd_H; ddestruct dd_H as (R1 & R10 & R11 & R12 & R14 & KC)).
        ddestruct (a_entry r1 ret 0 n Hret R1 R10 R11 R12 R14 ltac:(lia) ltac:(rewrite Z.add_0_r; exact Hal) ltac:(lia))
          as (r2 & RUN & A10 & K2).
        exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x46960 : word) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = at_ s 0 /\ getr r 11 = Z_to_bv 64 0
                         /\ getr r 12 = Z_to_bv 64 n /\ getr r 15 = at_ s (0 + 1) /\ getr r 16 = Z_to_bv 64 1
                         /\ keeps_cs regs r)).
      + eexists. split.
        * stepn F_431f8 D_431f8. rwH. vals_lit.     (* [comment removed for export] *)
          stepn F_431fc D_431fc.                    (* [comment removed for export] *)
          stepn F_43200 D_43200. snez1.             (* [comment removed for export] *)
          stepb_ft F_43204 D_43204
            ltac:(rwH; unfold c_eq, bv_eqb; rewrite andi7_u by lia; unorm; apply Z.eqb_neq;
                  rewrite Z.add_0_r; exact Hal).    (* [comment removed for export] *)
          stepb_ft F_43208 D_43208 ltac:(cond).     (* [comment removed for export] *)
          stepn F_4320c D_4320c.                    (* [comment removed for export] *)
          stepn F_43210 D_43210.                    (* [comment removed for export] *)
          apply mst_refl.
        * post.
      + cbv beta. (intros r1 dd_H; ddestruct dd_H as (R1 & R10 & R11 & R12 & R15 & R16 & KC)).
        ddestruct (h_loop (Z.to_nat (7 - bv_unsigned s mod 8)) r1 ret 0 n Hret R1 R10 R11 R12 R15 R16
                    ltac:(lia) ltac:(rewrite Z.add_0_r; lia) ltac:(lia)) as (r2 & RUN & A10 & K2).
        exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End MCHR.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem ref_memchr0 : ltac2:(CDefT.buildp (gd_tbl_P_memchr ()) "Pmem,P,(7.&40.)(1=.(7.&8.))Ps,(7.&40.)Pbuf,(14.(7.&8.))PK,$8.Pn,$8.Prom,P,(7.&40.)(1=.(7.&8.))Pregs,(2=.&5.(7.&40.))Pret,(7.&40.)P,(3;.R8.R7.R6.R5.R4.)P,(2>.R2.)P,(<.(7.&40.)(2?.R4.(30.&5.+1.$31.))R3.)P,(<.(7.&40.)(2?.R5.(30.&5.+:.$31.))R:.)P,(<.(7.&40.)(2?.R6.(30.&5.+;.$31.))(3.&40.=))P,(<.(7.&40.)(2?.R7.(30.&5.+<.$31.))(3.&40.R9.))(1?.(2=.&5.(7.&40.))Lregs',(2=.&5.(7.&40.))(:.(32.$21.(33.$34.R9.(30.&40.+46944.$31.)R?.R:.)(33.$34.R1.R8.R?.R:.))(:.(35.R9.R1.)(<.(7.&40.)(2?.R1.(30.&5.+:.$31.))(3.&40.(27.(9.&40.R>.)R<.))))))")
(* [comment removed for export] *).
Proof.
  intros mem s buf K n rom regs ret HOK Hret H1 H10 H11 H12.
  ddestruct (memchr0_run mem s buf K n rom HOK regs ret Hret H1 H10 H11 H12) as (r & RUN & A10 & KC).
  exists r. split; [exact RUN | split; [exact KC | exact A10]].
Qed.
