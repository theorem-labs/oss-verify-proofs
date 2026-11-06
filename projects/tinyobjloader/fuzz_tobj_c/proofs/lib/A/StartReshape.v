(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Datatypes"; "option"; "bool"; "false"; "Some"; "true"; "list"; "andb"; "nat"; "orb"; "None"; "prod"; "pair"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "True"; "not"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "cell"; "valuation"; "ob_hi"; "ob_lo"; "ob_base"; "eval"; "obj_holds"; "odefault"; "c_off"; "c_width"; "rd"; "SLit"; "image_byte"; "ob_cells"; "rm"; "ob_dflt"; "obj_range"; "c_val"; "pairwise_disjoint"; "rom_ok"; "tfact"; "dflt_writable"; "in_cell"; "mem_match"; "rl"; "rw"; "smatch"; "ss_objs"; "sv_eqb"; "DArr"; "DImage"; "DList"; "DRom"; "DZero"; "cell_holds"; "covered"; "outside_all"; "ranges_disjoint"; "soff"; "sstate"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartReshape"; "lit_small"; "binfo"; "find_cov"; "BRd"; "zseq"; "byte_info"; "cell_byte"; "lit_byte"; "obj_byte"; "BLit"; "all_lit_offs"; "lit_of"; "BImg"; "BNone"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@Stdlib.ZArith.BinInt.Z"; "add"; "leb"; "le"; "lt"; "modulo"; "pow"; "sub"; "eqb"; "to_nat"; "ltb"; "opp"; "mul"; "of_nat"; "shiftr"; "@Stdlib.Lists.List"; "forallb"; "In"; "existsb"; "nth_error"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "wview"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "in_ranges"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartReshape.Check"; "objT_ok"; "dflt_byte_ok"; "cov_idx"; "byte_is"; "cellT_ok"; "covered_litb"; "find_cov_idx"; "fview"; "pairwise_b"; "reshape_ok"; "disjT_b"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Init.Peano"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "cell_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "sub_range"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundW SymFrame SymEntail SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition lit_of (e : sv) : option Z := match e with SLit z => Some z | _ => None end.

Definition lit_small (e : sv) : option Z := ltac2:(tb__ "0|6|
S16S3S0A1M0Le;Ve;S0S4G0L_;S9S52S5bS56Z2Z3eA2M1A1R1A2S52R1G1A2A2S6S0R1A2ScS0A1M2X4x2Lz;S1G2Li;S7bS16S16G2Lb;La;M3Lop;M4G4S7cG3Lop;M5G5S4S2S16G2La;Lw;Lsgn;S1S16S0G2Lk;Li;Ll;X16x8").

Fixpoint zseq (lo : Z) (n : nat) : list Z :=
  match n with O => [] | S n' => lo :: zseq (lo + 1) n' end.

Lemma In_zseq : ltac2:(tb__ "0|0|
SaS0S0S14S60S0R1S44R2R3A2A3S10S53R2R1A2S54R1S51R2S5dR3A1A2A2A2A2Fz;Flo;Fn;").
Proof.
  induction n as [|n IH]; intros lo z; cbn [zseq].
  - split; [intros [] | intros H; lia].
  - rewrite Nat2Z.inj_succ. split.
    + intros [<-|H]; [lia|]. apply IH in H. lia.
    + intros H. destruct (Z.eq_dec lo z); [left; lia | right]. apply IH. lia.
Qed.

Inductive binfo := BNone | BRd | BLit (v : Z) | BImg.

Definition binfo_eqb (a b : binfo) : bool := ltac2:(tb__ "0|2|
S41S4La;Va;S41S4Lb;M0Vb;S7S5S0S5Lv;M1S5X41x4G0Vb;S5S7G1S5X41x4S0G0Vb;S5S5S0S58R2R1A2Ly;S5X41x4Lx;G0Vb;S5S5G1S7X41x4X41x4").

Definition lit_byte (z j : Z) : Z := ltac2:(tb__ "0|0|
S55S5eS55Vz;S56Z2Z40A2A2S5cZ8Vj;A2A2Z100A2").

Definition covers_b (o : sobj) (base : sv) (off : Z) : bool := ltac2:(tb__ "0|1|
S9S9S33S1bVo;A1Vbase;A2S3S0A1S4Lx;M0S40S1aVo;A1A1S0G0S40S19Vo;A1A1S0S9S52R2Voff;A2S5aVoff;R1A2A2Lhi;S5X3x2Llo;S5X3x2A2S2cS26Vo;A1A1A2").

Fixpoint find_cov (L : list sobj) (base : sv) (off : Z) : option sobj :=
  match L with
  | [] => None
  | o :: r => if covers_b o base off then Some o else find_cov r base off
  end.

Fixpoint cell_byte (cells : list cell) (off : Z) : option (option Z) :=
  match cells with
  | [] => None
  | c :: r =>
      match lit_small (c_off c) with
      | Some co => if (co <=? off) && (off <? co + c_width c) && (c_width c <=? 8)
                   then Some (match lit_of (c_val c) with Some z => Some (lit_byte z (off - co)) | None => None end)
                   else cell_byte r off
      | None => cell_byte r off
      end
  end.

Definition all_lit_offs (cells : list cell) : bool := ltac2:(tb__ "0|0|
S5fS17S17S3S0A1S4Lx;S40S1fR1A1A1S0S52S20R2A1Z8A2Lz;S5X3x2Lc;Vcells;A3").

Definition obj_byte (o : sobj) (off : Z) : binfo := ltac2:(tb__ "0|3|
S3S3S0A1M0A1S41Lx;S46S24Vo;A1M1Voff;A2G0G0S41Lo0;R1S0S49R1A1Lv;S43X3x2Lo0;S4S41L_;S4aG1A1S1eS41Lx;S26Vo;A1S43S49Z0A1S4cS1S43Ll;M2G2S0S16S8SdS0S0A2A1S8S2bA1S43Ltmpl;Lflds;Lcnt;Lesz;X1ex6S43X4x2X3x2").

Definition byte_info (L : list sobj) (base : sv) (off : Z) : binfo := ltac2:(tb__ "0|0|
S3S15A1S41Lx;S42VL;Vbase;Voff;A3S15S48R1Voff;A2Lo;S4dX3x2").

Section Check.
Variable segs : list Segment.

Definition byte_is (L : list sobj) (base : sv) (off : Z) (v : Z) : bool := ltac2:(tb__ "0|4|
S41S4Lx;S45VL;Vbase;Voff;A3S5S5S0S58S55R1Z100M0A2S55Vv;G0A2M1A2Lv';S9S33Vbase;S22Z0A1A2S3S4eQ8M2A1M3A1S4Lx;S23Vsegs;S4fQ40Voff;A2A2G3S58S50G2R1A2G1A2Lb;S5X3x2A2X41x4").

Definition cellT_ok (L : list sobj) (base : sv) (lo hi : Z) (c : cell) : bool := ltac2:(tb__ "0|3|
S3S0A1S4Lx;M0S40S1fVc;A1A1S0S9S9S9S9S52Vlo;R1A2S52S51R1S20Vc;A1M1A2Vhi;A2A2S5aZ0M2G1A2A2S52G1Z8A2A2G0S4bS28Vc;A1A1S0S5fS0S0S6bVL;Vbase;S51R3R1A2S47R2R1A2A4Lj;S44G2S59G1A1A2A3Lz;S3S15A1S4Lx;S42VL;Vbase;R1A3S15S61S17S7dVc;A1S24R1A1A3Lo;S5X3x2X3x2A2Lco;S5X3x2").

Definition covered_litb (cells : list cell) (off : Z) : bool := ltac2:(tb__ "0|0|
S61S17S17S3S0A1S4Lx;S40S1fR1A1A1S0S9S52R1Voff;A2S5aVoff;S51R1S20R2A1A2A2A2Lco;S5X3x2Lc;Vcells;A3").

Definition dflt_byte_ok (L : list sobj) (base : sv) (d : odefault) (off : Z) : bool := ltac2:(tb__ "0|3|
S1eS4Ld;Vd;S7S41S4Lx;M0S45VL;Vbase;Voff;A3M1S5S5S0S58S55R1Z100A2Z0A2Lv;S5X41x4G0G1S5S5S0S5Lv;S7X41x4S1S5Ll;M2G2S0S16S8SdS0S0A2A1S8S2bA1S5Ltmpl;Lflds;Lcnt;Lesz;X1ex6").

Definition objT_ok (L : list sobj) (o : sobj) : bool := ltac2:(tb__ "0|b|
S3S0A1S4Lx;M0S40S1aVo;A1A1S0G0S40S19Vo;A1A1S0S9S9S9S9S52R2R1A2S1eS4Lx;M1S26Vo;A1M2S7S7S7S1S5Ll;M3G3S0S16S8SdS0S0A2A1M4S8S2bA1M5S5Ltmpl;Lflds;Lcnt;Lesz;X1ex6A2S3S15A1S4Lx;S42VL;S1bVo;A1M6R2A3S15G0S40S19R1A1A1S0S52R3R1A2Lhic;S5X3x2Loc;S5X3x2A2S5fS17S6cVL;G6R2R1A4S24Vo;A1M7A3A2G1G2S7S5fS0S0SbS6dG7R1A2M8S69VL;G6S38R1A4A2Loff;S44R2S59S57R1R2A2A1A2M9A3S5fS0S0SbG8S69VL;G6S35R1A4A2Loff;G9A3S1S5fS0S0SbG8S69VL;G6S36R2A1R1A4A2Loff;S44R3S59S57R2R3A2A1A2MaA3Ll;S1S5fS0S0SbG8S69VL;G6S37R2A1R1A4A2Loff;GaA3Ll;S0S16G4G5S5fS0S0SbG8S69VL;G6S34R5R4R3R2A4R1A4A2Loff;S44R6S59S57R5R6A2A1A2A3Ltmpl;Lflds;Lcnt;Lesz;X1ex6A2Lhi;S5X3x2Llo;S5X3x2").

Fixpoint find_cov_idx (L : list sobj) (base : sv) (off : Z) (n : nat) : option nat :=
  match L with
  | [] => None
  | o :: r => if covers_b o base off then Some n else find_cov_idx r base off (S n)
  end.

Definition cov_idx (L : list sobj) (o : sobj) : option nat := ltac2:(tb__ "0|0|
S3S0A1S3SaA1Lx;S40S1aVo;A1A1S0S6eVL;S1bVo;A1R1U0A4Llo;ScSaA1X3x2").

Definition disjT_b (L : list sobj) (o1 o2 : sobj) : bool := ltac2:(tb__ "0|2|
S3SaA1S4Lx;M0S6aVL;Vo1;A2SaG0S6aVL;Vo2;A2SaS4S4L_;S7fR2R1A2S3S0A1S4Lx;M1S40S1aVo1;A1A1S0G1S40S19Vo1;A1A1S0G1S40S1aVo2;A1A1S0G1S40S19Vo2;A1A1S0SbSbSbS52R3R4A2S52R1R2A2A2S52R3R2A2A2S52R1R4A2A2Lh2;S5X3x2Ll2;S5X3x2Lh1;S5X3x2Ll1;S5X3x2S7X4x2Lj;S5X3x2Li;S5X3x2").

Fixpoint pairwise_b (L : list sobj) (T : list sobj) : bool :=
  match T with
  | [] => true
  | o :: r => forallb (disjT_b L o) r && pairwise_b L r
  end.

Definition reshape_ok (L T : list sobj) : bool := ltac2:(tb__ "0|0|
S9S5fS15S68VL;A1VT;A3S70VL;VT;A2A2").

Lemma lit_of_Some : ltac2:(tb__ "0|0|
S16S0SfS3S0A1S4bR2A1S6S0R1A2A3SfS16R3S22R2A1A3F_;Fz;Fe;").
Proof. intros e z H. destruct e; cbn in H; try discriminate. congruence. Qed.
Lemma lit_small_Some : ltac2:(tb__ "0|1|
S16S0SfS3S0A1S40R2A1S6S0R1A2A3S10SfS16R3S22R2A1A3S10S53S5bS56Z2Z3eA2M0A1R2A2S53R2G0A2A2A2F_;Fz;Fe;").
Proof.
  intros e z H. destruct e; cbn -[Z.leb Z.pow Z.opp] in H; try discriminate.
  destruct ((- 2 ^ 62 <=? z0) && (z0 <=? 2 ^ 62)) eqn:E; [|discriminate]. injection H as <-.
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. split; [reflexivity | lia].
Qed.
Lemma soff_small : ltac2:(tb__ "0|0|
S18S16S0SfS3S0A1S40R2A1S6S0R1A2A3SfS0S3dR4R3A2R2A3F_;Fz;Fe;Frho;").
Proof. intros rho e z H. apply lit_small_Some in H as [-> Hz]. apply soff_lit_small. lia. Qed.

Lemma Z_to_bv8_mod256 : ltac2:(tb__ "0|2|
S0S0SfS0S55R2Z100M0A2S55R1G0A2A3SfS4eQ8M1A1S4fG1R3A2S4fG1R2A2A3F_;Fb;Fa;").
Proof.
  intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. exact H.
Qed.

Lemma find_cov_spec : ltac2:(tb__ "0|1|
S8S15A1S16S0S15SfS3S15A1S42R4R3R2A3S6S15R1A2A3S10S60S15R2R5A3S10SfS16S1bR2A1R4A3S11S0S0S11S0S0S10SfS3S0A1M0S40S1aR4A1A1S6S0R2A2A3S10SfG0S40S19R4A1A1S6S0R1A2A3S10S10S53R2R5A2S54R5R1A2A2SfS4S2cS26R4A1A1S7A3A2A2A2Lhi;A2Llo;A2A2A2F_;Fo;Foff;Fbase;FL;").
Proof.
  induction L as [|o' L IH]; intros base off o H; cbn [find_cov] in H; [discriminate|].
  destruct (covers_b o' base off) eqn:E.
  - injection H as <-. split; [left; reflexivity|]. unfold covers_b in E.
    apply andb_prop in E as [E W]. apply andb_prop in E as [E1 E2]. apply sv_eqb_sound in E1. split; [exact E1|].
    destruct (lit_small (ob_lo o')) as [lo|] eqn:EL; [|discriminate]. destruct (lit_small (ob_hi o')) as [hi|] eqn:EH; [|discriminate].
    exists lo, hi. split; [reflexivity|]. split; [reflexivity|].
    apply andb_prop in E2 as [E2 E3]. apply Z.leb_le in E2. apply Z.ltb_lt in E3. split; [lia | exact W].
  - destruct (IH base off o H) as (H1 & H2). split; [right; exact H1 | exact H2].
Qed.

Lemma find_cov_idx_spec : ltac2:(tb__ "0|2|
S8S15A1S16S0SaSaSfS3SaA1S6eR5R4R3R2A4S6SaR1A2A3S11S15S15S10SfS3S15A1M0S42R7R6R5A3S6S15R1A2M1A3S10SfG0S62S15R7S77R3R4A2A3G1A3S78R4R3A2A2A2Lo;A2F_;Fi;Fn;Foff;Fbase;FL;").
Proof.
  induction L as [|o L IH]; intros base off n i H; cbn [find_cov_idx find_cov] in H |- *; [discriminate|].
  destruct (covers_b o base off) eqn:E.
  - injection H as <-. exists o. split; [reflexivity|]. rewrite Nat.sub_diag. split; [reflexivity | lia].
  - destruct (IH base off (S n) i H) as (o' & H1 & H2 & H3). exists o'. split; [exact H1|].
    replace (i - n)%nat with (S (i - S n)) by lia. cbn [nth_error]. split; [exact H2 | lia].
Qed.

Lemma cell_byte_spec : ltac2:(tb__ "0|2|
S8S17A1S0S3S0A1M0SfS3G0A1S46R3R2A2S6G0R1A2A3S11S17S17S11S0S0S10S60S17R2R6A3S10SfG0S40S1fR2A1A1S6S0R1A2A3S10S10S53R1R5A2S54R5S51R1S20R2A1M1A2A2A2S10S53G1Z8A2G0OLr;R4S0S11S0S0S10SfS16S28R4A1S22R1A1A3SfS0R2S47R1S57R7R3A2A2A3A2Lz;A2Lv;S12X3x2A2A2A2A2Lco;A2Lc;A2F_;Fr;Foff;Fcells;").
Proof.
  induction cells as [|c cells IH]; intros off r H; cbn [cell_byte] in H; [discriminate|].
  destruct (lit_small (c_off c)) as [co|] eqn:EO.
  - destruct ((co <=? off) && (off <? co + c_width c) && (c_width c <=? 8)) eqn:E.
    + injection H as <-. exists c, co. repeat (apply andb_prop in E as [E ?]).
      apply Z.leb_le in E. apply Z.ltb_lt in H0. apply Z.leb_le in H.
      split; [left; reflexivity|]. split; [exact EO|]. split; [lia|]. split; [lia|].
      destruct (lit_of (c_val c)) as [z|] eqn:EV; [|exact I]. exists z. split; [apply lit_of_Some; exact EV | reflexivity].
    + destruct (IH off r H) as (c' & co' & H1 & H2). exists c', co'. split; [right; exact H1 | exact H2].
  - destruct (IH off r H) as (c' & co' & H1 & H2). exists c', co'. split; [right; exact H1 | exact H2].
Qed.

Lemma cell_byte_none : ltac2:(tb__ "0|1|
S18S8S17A1S0SfS3S3S0A1M0A1S46R2R1A2ScG0A1A3SfS4S4aR3A1S7A3S17S60S17R1R5A3S13S2dR7R5R2A3A1F_;Fc;F_;F_;Foff;Fcells;Frho;").
Proof.
  induction cells as [|c cells IH]; intros off H Hall c' Hin; [destruct Hin|].
  cbn [cell_byte] in H. unfold all_lit_offs in Hall. cbn [forallb] in Hall. apply andb_prop in Hall as [Hl Hall].
  destruct (lit_small (c_off c)) as [co|] eqn:EO; [|discriminate]. apply Z.leb_le in Hl.
  destruct ((co <=? off) && (off <? co + c_width c) && (c_width c <=? 8)) eqn:E; [discriminate|].
  destruct Hin as [<-|Hin].
  - unfold in_cell. rewrite (soff_small rho _ _ EO).
    apply Bool.andb_false_iff in E. destruct E as [E|E]; [apply Bool.andb_false_iff in E; destruct E as [E|E]|];
      [apply Z.leb_gt in E | apply Z.ltb_ge in E | apply Z.leb_gt in E]; lia.
  - exact (IH off H Hall c' Hin).
Qed.

Lemma covered_litb_false : ltac2:(tb__ "0|0|
S18S8S17A1S0SfS4S6dR2R1A2S5A3SfS4S5fS17S17S3S0A1S4Lx;S40S1fR1A1A1S0S7Lz;S5X3x2Lc;R3A3S7A3S13S3aR5R4R3A3A1F_;F_;Foff;Fcells;Frho;").
Proof.
  intros rho cells off H Hl Hc. unfold covered in Hc. apply Exists_exists in Hc as (c & Hin & Hic).
  unfold covered_litb in H. pose proof (proj1 (forallb_forall _ _) Hl c Hin) as X. cbn beta in X.
  destruct (lit_small (c_off c)) as [co|] eqn:EO; [|discriminate].
  assert (E : existsb (fun c0 => match lit_small (c_off c0) with Some co0 => (co0 <=? off) && (off <? co0 + c_width c0) | None => false end) cells = true).
  { apply existsb_exists. exists c. split; [exact Hin|]. rewrite EO. unfold in_cell in Hic. rewrite (soff_small rho _ _ EO) in Hic.
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  rewrite E in H. discriminate.
Qed.

Section Sound.
Variable rho : valuation.
Variable ms : machine_state.
Variable L : list sobj.
Hypothesis HL : ltac2:(tb__ "0|0|
S73S15S1dVsegs;Vrho;Vms;A3VL;A3").
Hypothesis Hrom : rom_ok segs ms.

Lemma U64 : bv_modulus 64 = 2 ^ 64. Proof. reflexivity. Qed.

Let B (o : sobj) : Z := ltac2:(tb__ "0|0|
S50Q40S1cVrho;S1bVo;A1A2A2").

Lemma lit_cell_byte : ltac2:(tb__ "0|2|
S15S17S0S0S0S1dVsegs;Vrho;Vms;R5A4S60S17R5S24R6A1A3SfS3S0A1S40S1fR6A1A1S6S0R5A2A3SfS16S28R7A1S22R5A1A3S10S53R7R5A2S54R5S51R7S20R8A1A2A2A2S53S20R9A1Z8A2SfS3S4eQ8M0A1M1A1S21Vms;S4fQ40S51VB;RbA1R7A2A2A2S6G1S4fG0S47R8S57R7R9A2A2A2A2A3F_;F_;F_;F_;F_;F_;Foff;Fz;Fco;Fc;Fo;").
Proof.
  intros o c co z off (Hb & _ & Hc & _) Hin Hco Hz Hoff Hk8.
  pose proof (proj1 (Forall_forall _ _) Hc _ Hin) as (C1 & C2 & C3).
  destruct Hb as (B1 & B2 & B3 & B4). unfold obj_lo_of, obj_hi_of in *. rewrite (soff_small rho _ _ Hco) in C1, C2, C3.
  assert (UO : bv_unsigned (oaddr rho (ob_base o) co) = B o + co).
  { unfold oaddr, B. rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite U64. unfold B in *. lia. }
  pose proof (rd_bytes_nth ms (Z.to_nat (c_width c)) (oaddr rho (ob_base o) co) _ (Z.to_nat (off - co)) C3 ltac:(lia) ltac:(rewrite UO; unfold B in *; lia)) as R.
  rewrite UO, Z2Nat.id in R by lia. replace (B o + co + (off - co)) with (B o + off) in R by lia.
  rewrite R. f_equal. unfold enc_bytes. rewrite Z_to_le_bytes_nth by lia. rewrite Hz. cbn [eval]. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite U64.
  rewrite Z2Nat.id by lia. apply Z_to_bv8_mod256. unfold lit_byte. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma cell_rd : ltac2:(tb__ "0|1|
S15S17S0S1dVsegs;Vrho;Vms;R3A4S60S17R3S24R4A1A3S2dVrho;R3R4A3S11S4eQ8A1M0G0SfS3G0A1S21Vms;S4fQ40S51VB;R7A1R5A2A2A2S6G0R1A2A3Lb;A2F_;F_;F_;Foff;Fc;Fo;").
Proof.
  intros o c off (Hb & _ & Hc & _) Hin Hic.
  pose proof (proj1 (Forall_forall _ _) Hc _ Hin) as (C1 & C2 & C3). unfold in_cell in Hic.
  destruct Hb as (B1 & B2 & B3 & B4). unfold obj_lo_of, obj_hi_of in *.
  assert (UO : bv_unsigned (oaddr rho (ob_base o) (soff rho (c_off c))) = B o + soff rho (c_off c)).
  { unfold oaddr, B. rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite U64. unfold B in *. lia. }
  pose proof (rd_bytes_nth ms (Z.to_nat (c_width c)) (oaddr rho (ob_base o) (soff rho (c_off c))) _ (Z.to_nat (off - soff rho (c_off c))) C3
                ltac:(lia) ltac:(rewrite UO; unfold B in *; lia)) as R.
  rewrite UO, Z2Nat.id in R by lia. replace (B o + soff rho (c_off c) + (off - soff rho (c_off c))) with (B o + off) in R by lia.
  eexists. exact R.
Qed.

Lemma obj_byte_sound : ltac2:(tb__ "0|8|
S15S0S0S0S1dVsegs;Vrho;Vms;R4A4SfS3S0A1M0S40S1aR5A1A1S6S0R4A2M1A3SfG0S40S19R6A1A1G1A3S10S53R6R4A2S54R4R5A2A2S4fQ40M2S51VB;R8A1R5A2A2S4eG2A1S10S11S4eQ8M3A1M4G4SfS3G4A1M5S21Vms;R2A2M6S6G4R1A2M7A3Lb;A2S41OLx;S48R9R6A2S12S12S0SfG5G6S6G4S4fG3R1A2A2A3Lv;S10SfG5S64Vms;R1A2ScG4A1A3S11G4G4SfG5S23Vsegs;R2A2G7A3Lb;A2A2X41x4A2Ta;F_;F_;F_;F_;Foff;Fhi;Flo;Fo;").
Proof.
  intros o lo hi off Ho Hlo Hhi Hoff a.
  pose proof Ho as (Hb & Hw & Hc & Hd & _). unfold obj_lo_of, obj_hi_of in *.
  rewrite (soff_small rho _ _ Hlo), (soff_small rho _ _ Hhi) in Hb, Hw, Hc, Hd.

  assert (RD : exists b, rd ms a = Some b).
  { assert (DEC : forall c, {in_cell rho off c} + {~ in_cell rho off c}).
    { intros c0. unfold in_cell. destruct (Z_le_dec (soff rho (c_off c0)) off); [destruct (Z_lt_dec off (soff rho (c_off c0) + c_width c0)); [left; lia | right; lia] | right; lia]. }
    destruct (Exists_dec (in_cell rho off) (ob_cells o) DEC) as [Hcov|Hncov].
    - apply Exists_exists in Hcov as (c & Hin & Hic). exact (cell_rd o c off Ho Hin Hic).
    - specialize (Hd off Hoff Hncov). subst a. unfold B. destruct (ob_dflt o); cbn in Hd.
      + exact Hd.
      + eexists; exact Hd.
      + destruct Hd as [Hn [b Hib]]. exists b. unfold rd, ms_read_byte. rewrite Hn. rewrite (Hrom _). exact Hib.
      + eexists; exact Hd.
      + eexists; exact Hd.
      + exact Hd. }
  split; [exact RD|].
  unfold obj_byte. destruct (cell_byte (ob_cells o) off) as [r|] eqn:EC.
  - destruct (cell_byte_spec _ _ _ EC) as (c & co & Hin & Hco & Hr & Hk8 & Hv). destruct r as [v|]; [|exact I].
    destruct Hv as (z & Hz & ->). subst a. exact (lit_cell_byte o c co z off Ho Hin Hco Hz Hr Hk8).
  - destruct (all_lit_offs (ob_cells o)) eqn:EA; [|exact I].
    assert (NC : ~ covered rho (ob_cells o) off).
    { intros Hcov. unfold covered in Hcov. apply Exists_exists in Hcov as (c & Hin & Hic). exact (cell_byte_none rho _ _ EC EA c Hin Hic). }
    specialize (Hd off Hoff NC). subst a. unfold B. destruct (ob_dflt o); cbn in Hd; try exact I.
    + exact Hd.
    + exact Hd.
Qed.

Lemma byte_info_sound : ltac2:(tb__ "0|9|
S16S0S15SfS3S15A1S42VL;R3R2A3S6S15R1A2A3S4fQ40M0S51S50G0S1cVrho;R4A2A2R3A2A2S4eG0A1S10S1dVsegs;Vrho;Vms;R3A4S10SfS0VB;R3A1S50G0S1cVrho;R5A2A2M1A3S10S10S53Z0S51G1R4A2M2A2S54G2S56Z2Z40A2A2A2S10S13SfS3S4eQ8M3A1M4A1M5S65Vsegs;S64Vms;A1R1A3ScG4A1M6A3A1S10S11G4G4SfG5S21Vms;R2A2M7S6G4R1A2M8A3Lb;A2S41OLx;S45VL;R5R4A3S12S12S0SfG5G7S6G4S4fG3R1A2A2A3Lv;S10SfG5S64Vms;R1A2G6A3S11G4G4SfG5S23Vsegs;R2A2G8A3Lb;A2A2X41x4A2A2A2A2A2Ta;F_;Fo;Foff;Fbase;").
Proof.
  intros base off o Hf a.
  destruct (find_cov_spec _ _ _ _ Hf) as (Hin & Hbase & lo & hi & Hlo & Hhi & Hoff & HW).
  pose proof (proj1 (Forall_forall _ _) HL o Hin) as Ho.
  assert (EB : B o = bv_unsigned (eval rho base)) by (unfold B; rewrite Hbase; reflexivity).
  pose proof Ho as (Hb & Hw & _). unfold obj_lo_of, obj_hi_of in Hb, Hw.
  rewrite (soff_small rho _ _ Hlo), (soff_small rho _ _ Hhi) in Hb, Hw. rewrite Hbase in Hb, Hw.
  split; [exact Ho|]. split; [exact EB|]. split; [lia|]. split; [exact (Hw off Hoff HW)|].
  pose proof (obj_byte_sound o lo hi off Ho Hlo Hhi Hoff) as X. cbv zeta in X. rewrite EB in X.
  destruct X as [X1 X2]. split; [exact X1|]. unfold byte_info. rewrite Hf. exact X2.
Qed.

Lemma byte_is_sound : ltac2:(tb__ "0|3|
S16S0S0SfS4S6bVL;R3R2R1A4S7A3SfS3S4eQ8M0A1M1A1S21Vms;S4fQ40M2S51S50G2S1cVrho;R4A2A2R3A2A2A2S6G1S4fG0R2A2A2A3F_;Fv;Foff;Fbase;").
Proof.
  intros base off v H. unfold byte_is in H.
  destruct (find_cov L base off) as [o|] eqn:Hf.
  2:{ unfold byte_info in H. rewrite Hf in H. discriminate. }
  pose proof (byte_info_sound base off o Hf) as X. cbv zeta in X. destruct X as (Ho & EB & Hr & HWv & HRd & Hbi).
  destruct (byte_info L base off) as [| |v'|]; try discriminate.
  - apply Z.eqb_eq in H. rewrite Hbi. f_equal. apply Z_to_bv8_mod256. exact H.
  - apply andb_prop in H as [Hb0 Hib]. apply sv_eqb_sound in Hb0. subst base.
    destruct Hbi as [Hn [b Hb]]. cbn [eval] in *. rewrite Z_to_bv_unsigned in *. change (bv_wrap 64 0) with 0 in *. rewrite Z.add_0_l in *.
    rewrite Hb in Hib. apply Z.eqb_eq in Hib.
    unfold rd, ms_read_byte. rewrite Hn, (Hrom _), Hb. f_equal.
    apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite <- Hib.
    first [reflexivity | rewrite Z.mod_small; [reflexivity | pose proof (bv_unsigned_in_range 8 b) as R; change (bv_modulus 8) with 256 in R; lia]].
Qed.

Lemma cellT_ok_sound : ltac2:(tb__ "0|1|
S16S0S0S17S0S0SfS4S6cVL;R6R5R4R3A5S7A3S53Z0S51S50Q40M0S1cVrho;R7A2A2R6A2A2S53S51S50G0S1cVrho;R8A2A2R6A2S56Z2Z40A2A2S39Vrho;R9R8R7Vms;R6A6F_;F_;F_;Fbhi;Fblo;Fc;Fhi;Flo;Fbase;").
Proof.
  intros base lo hi c blo bhi H Hl Hh. unfold cellT_ok in H.
  destruct (lit_small (c_off c)) as [co|] eqn:Hco; [|discriminate].
  apply andb_prop in H as [H Hv]. apply andb_prop in H as [H Hk8]. apply andb_prop in H as [H Hk0]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in Hk0. apply Z.leb_le in Hk8.
  unfold cell_holds. rewrite (soff_small rho _ _ Hco). split; [lia|]. split; [lia|].
  set (b := bv_unsigned (eval rho base)) in *.
  assert (UO : bv_unsigned (oaddr rho base co) = b + co).
  { unfold oaddr. subst b. rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite U64. lia. }
  destruct (lit_of (c_val c)) as [z|] eqn:Hz.
  - apply lit_of_Some in Hz.
    apply rd_bytes_of_nth.
    + unfold enc_bytes. rewrite Z_to_le_bytes_length. reflexivity.
    + rewrite UO. lia.
    + intros j Hj. rewrite UO. pose proof (proj1 (forallb_forall _ _) Hv (Z.of_nat j) ltac:(apply In_zseq; lia)) as Bj. cbn beta in Bj.
      replace (b + co + Z.of_nat j) with (b + (co + Z.of_nat j)) by lia. subst b. rewrite (byte_is_sound base (co + Z.of_nat j) _ Bj).
      f_equal. unfold enc_bytes. rewrite Z_to_le_bytes_nth by lia. rewrite Hz. cbn [eval]. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite U64.
      apply Z_to_bv8_mod256. unfold lit_byte. rewrite Z.mod_mod by lia. reflexivity.
  - destruct (find_cov L base co) as [o|] eqn:Hf; [|discriminate].
    apply existsb_exists in Hv as (c' & Hin & Heq). apply cell_eqb_sound in Heq. subst c'.
    destruct (find_cov_spec _ _ _ _ Hf) as (HinL & Hbase & loL & hiL & HloL & HhiL & HoffL & _).
    pose proof (proj1 (Forall_forall _ _) HL o HinL) as (Hb & _ & Hc & _).
    pose proof (proj1 (Forall_forall _ _) Hc c Hin) as (C1 & C2 & C3). rewrite Hbase, (soff_small rho _ _ Hco) in C3. exact C3.
Qed.

Lemma objT_ok_sound : ltac2:(tb__ "0|0|
S15SfS4S68VL;R1A2S7A3S1dVsegs;Vrho;Vms;R2A4F_;Fo;").
Proof.
  intros o H. unfold objT_ok in H.
  destruct (lit_small (ob_lo o)) as [lo|] eqn:Hlo; [|discriminate]. destruct (lit_small (ob_hi o)) as [hi|] eqn:Hhi; [|discriminate].
  apply andb_prop in H as [H Hdf]. apply andb_prop in H as [H Hcells]. apply andb_prop in H as [H Hcov]. apply andb_prop in H as [Hlohi Hd].
  apply Z.leb_le in Hlohi.
  destruct (find_cov L (ob_base o) lo) as [oc|] eqn:Hf; [|discriminate].
  destruct (lit_small (ob_hi oc)) as [hic|] eqn:Hhic; [|discriminate]. apply Z.leb_le in Hcov.
  destruct (find_cov_spec _ _ _ _ Hf) as (HinL & Hbase & loc & hic' & Hloc & Hhic' & Hoffc & HWc).
  rewrite Hhic in Hhic'. injection Hhic' as <-.
  pose proof (proj1 (Forall_forall _ _) HL oc HinL) as Hoc. pose proof Hoc as (Hbc & Hwc & _).
  unfold obj_lo_of, obj_hi_of in Hbc, Hwc. rewrite (soff_small rho _ _ Hloc), (soff_small rho _ _ Hhic), Hbase in Hbc, Hwc.
  pose proof (lit_small_Some _ _ Hlo) as [_ Rlo]. pose proof (lit_small_Some _ _ Hhi) as [_ Rhi].
  set (b := bv_unsigned (eval rho (ob_base o))) in *.

  assert (INB : forall off, lo <= off < hi -> exists o', find_cov L (ob_base o) off = Some o').
  { intros off Hoff. clear -Hf Hloc Hhic Hoffc Hcov Hoff Hbase HWc.
    revert Hf. induction L as [|o1 L1 IH]; cbn [find_cov]; intros Hf; [discriminate|].
    destruct (covers_b o1 (ob_base o) lo) eqn:E.
    - injection Hf as ->. assert (E2 : covers_b oc (ob_base o) off = true).
      { unfold covers_b in E |- *. rewrite Hloc, Hhic in *. apply andb_prop in E as [E W]. apply andb_prop in E as [E1 _].
        rewrite E1, W. rewrite (proj2 (Z.leb_le loc off)), (proj2 (Z.ltb_lt off hic)) by lia. reflexivity. }
      rewrite E2. eexists; reflexivity.
    - destruct (covers_b o1 (ob_base o) off); [eexists; reflexivity | exact (IH Hf)]. }
  unfold obj_holds. unfold obj_lo_of, obj_hi_of. rewrite (soff_small rho _ _ Hlo), (soff_small rho _ _ Hhi). fold b.
  split; [lia|]. split.
  { intros off Hoff _. destruct (INB off Hoff) as [o' Hf']. destruct (byte_info_sound (ob_base o) off o' Hf') as (_ & _ & _ & W & _). exact W. }
  split.
  { apply Forall_forall. intros c Hin. apply (cellT_ok_sound (ob_base o) lo hi c lo hi (proj1 (forallb_forall _ _) Hcells c Hin)); lia. }
  split.
  2:{ destruct (ob_dflt o); try discriminate; exact I. }
  intros off Hoff Hnc. destruct (INB off Hoff) as [o' Hf'].
  pose proof (byte_info_sound (ob_base o) off o' Hf') as X. cbv zeta in X. fold b in X. destruct X as (Ho' & EB & Hr & HWv & HRd & Hbi).
  destruct (ob_dflt o) eqn:ED; try discriminate; cbn [dflt_holds].
  -   exact HRd.
  -   pose proof (proj1 (forallb_forall _ _) Hdf off ltac:(apply In_zseq; lia)) as X. cbn beta in X.
    destruct (covered_litb (ob_cells o) off) eqn:EC.
    { exfalso. unfold covered_litb in EC. apply existsb_exists in EC as (c & Hin & Hc). apply Hnc. unfold covered. apply Exists_exists. exists c. split; [exact Hin|].
      destruct (lit_small (c_off c)) as [co|] eqn:Hco; [|discriminate]. apply andb_prop in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc1. apply Z.ltb_lt in Hc2.
      unfold in_cell. rewrite (soff_small rho _ _ Hco). lia. }
    cbn [orb] in X. unfold dflt_byte_ok in X. destruct (byte_info L (ob_base o) off) as [| |v|]; try discriminate.
    apply Z.eqb_eq in X. rewrite Hbi. f_equal. apply Z_to_bv8_mod256. rewrite X. reflexivity.
  -   pose proof (proj1 (forallb_forall _ _) Hdf off ltac:(apply In_zseq; lia)) as X. cbn beta in X.
    destruct (covered_litb (ob_cells o) off) eqn:EC.
    { exfalso. unfold covered_litb in EC. apply existsb_exists in EC as (c & Hin & Hc). apply Hnc. unfold covered. apply Exists_exists. exists c. split; [exact Hin|].
      destruct (lit_small (c_off c)) as [co|] eqn:Hco; [|discriminate]. apply andb_prop in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc1. apply Z.ltb_lt in Hc2.
      unfold in_cell. rewrite (soff_small rho _ _ Hco). lia. }
    cbn [orb] in X. unfold dflt_byte_ok in X. destruct (byte_info L (ob_base o) off) as [| |v|]; try discriminate. exact Hbi.
Qed.

Lemma cov_idx_sound : ltac2:(tb__ "0|1|
S15SaSfS4S68VL;R2A2S7A3SfS3SaA1S6aVL;R3A2S6SaR2A2A3S11S15S15S11S0S0S11S0S0S10SfS3S15A1S62S15VL;R6A3S6S15R3A2A3S10SfS3S0A1M0S40S1aR7A1A1S6S0R2A2A3S10SfG0S40S19R7A1A1S6S0R1A2A3S10SfS16S1bR3A1S1bR7A1A3S7eS27Vrho;R7A2S27Vrho;R3A2A2A2A2A2A2Lhi;A2Llo;A2Loc;A2F_;F_;Fi;Fo;").
Proof.
  intros o i H Hc. unfold cov_idx in Hc. unfold objT_ok in H.
  destruct (lit_small (ob_lo o)) as [lo|] eqn:Hlo; [|discriminate]. destruct (lit_small (ob_hi o)) as [hi|] eqn:Hhi; [|discriminate].
  apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [H Hcov]. apply andb_prop in H as [Hlohi _]. apply Z.leb_le in Hlohi.
  destruct (find_cov_idx_spec _ _ _ _ _ Hc) as (oc & Hf & Hn & _). rewrite Nat.sub_0_r in Hn. rewrite Hf in Hcov.
  destruct (lit_small (ob_hi oc)) as [hic|] eqn:Hhic; [|discriminate]. apply Z.leb_le in Hcov.
  destruct (find_cov_spec _ _ _ _ Hf) as (HinL & Hbase & loc & hic' & Hloc & Hhic' & Hoffc & _). rewrite Hhic in Hhic'. injection Hhic' as <-.
  exists oc, lo, hi. split; [exact Hn|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hbase|].
  unfold sub_range, obj_range, obj_lo_of, obj_hi_of. cbn [fst snd].
  rewrite (soff_small rho _ _ Hlo), (soff_small rho _ _ Hhi), (soff_small rho _ _ Hloc), (soff_small rho _ _ Hhic), Hbase. lia.
Qed.

Lemma disjT_sound : ltac2:(tb__ "0|1|
S15S15SfS4S68VL;R2A2S7A3M0G0S29Vrho;VL;A2SfS4S72VL;R5R4A3S7A3S3cS27Vrho;R6A2S27Vrho;R5A2A2F_;F_;F_;F_;Fo2;Fo1;").
Proof.
  intros o1 o2 H1 H2 HPD H. unfold disjT_b in H.
  destruct (cov_idx L o1) as [i|] eqn:E1; [|discriminate]. destruct (cov_idx L o2) as [j|] eqn:E2; [|discriminate].
  destruct (cov_idx_sound o1 i H1 E1) as (oc1 & lo1 & hi1 & N1 & L1 & R1 & B1 & S1).
  destruct (cov_idx_sound o2 j H2 E2) as (oc2 & lo2 & hi2 & N2 & L2 & R2 & B2 & S2).
  destruct (Nat.eqb_spec i j) as [->|NE].
  - rewrite L1, R1, L2, R2 in H. rewrite N1 in N2. injection N2 as <-.
    unfold ranges_disjoint, obj_range, obj_lo_of, obj_hi_of. cbn [fst snd].
    rewrite (soff_small rho _ _ L1), (soff_small rho _ _ R1), (soff_small rho _ _ L2), (soff_small rho _ _ R2), <- B1, B2.
    repeat (apply Bool.orb_true_iff in H; destruct H as [H|H]); apply Z.leb_le in H; lia.
  - pose proof (SymSoundW.pairwise_disjoint_nth rho L i j oc1 oc2 HPD N1 N2 NE) as D.
    unfold ranges_disjoint, sub_range in *. lia.
Qed.

Lemma pairwise_sound : ltac2:(tb__ "0|0|
S8S15A1SfS4S5fS15S68VL;A1R1A3S7A3S29Vrho;VL;A2SfS4S70VL;R3A2S7A3S29Vrho;R4A2F_;F_;F_;FT;").
Proof.
  intros T. induction T as [|o T IH]; intros HT HPD H; cbn [pairwise_b pairwise_disjoint] in *; [exact I|].
  apply andb_prop in HT as [Ho HT]. apply andb_prop in H as [H1 H2]. split; [|exact (IH HT HPD H2)].
  apply Forall_forall. intros o' Hin. apply (disjT_sound o o' Ho (proj1 (forallb_forall _ _) HT o' Hin) HPD (proj1 (forallb_forall _ _) H1 o' Hin)).
Qed.

Lemma reshape_inside : ltac2:(tb__ "0|0|
S8S15A1S4eQ40A1SfS4S5fS15S68VL;A1R2A3S7A3S13S3bVrho;R3R2A3A1S67Vrho;VL;R3A3F_;F_;Fa;FT;").
Proof.
  intros T a HT Hno.
  assert (EX : exists o, In o T /\ fst (obj_range rho o) <= bv_unsigned a < snd (obj_range rho o)).
  { unfold outside_all in Hno. clear HT. induction T as [|o T IH].
    - exfalso. apply Hno. constructor.
    - destruct (Z_le_dec (fst (obj_range rho o)) (bv_unsigned a)); [destruct (Z_lt_dec (bv_unsigned a) (snd (obj_range rho o)))|].
      + exists o. split; [left; reflexivity | lia].
      + destruct IH as (o' & Hin & Hr); [intros HF; apply Hno; constructor; [cbn beta; lia | exact HF] | exists o'; split; [right; exact Hin | exact Hr]].
      + destruct IH as (o' & Hin & Hr); [intros HF; apply Hno; constructor; [cbn beta; lia | exact HF] | exists o'; split; [right; exact Hin | exact Hr]]. }
  destruct EX as (o & Hin & Hr). pose proof (proj1 (forallb_forall _ _) HT o Hin) as Ho.
  destruct (cov_idx L o) as [i|] eqn:Ec.
  - destruct (cov_idx_sound o i Ho Ec) as (oc & lo & hi & N & _ & _ & _ & S). exists oc. split; [eapply nth_error_In; exact N|]. unfold sub_range in S. lia.
  - exfalso. unfold cov_idx in Ec. unfold objT_ok in Ho. destruct (lit_small (ob_lo o)) as [lo|]; [|discriminate]. destruct (lit_small (ob_hi o)); [|discriminate].
    apply andb_prop in Ho as [Ho _]. apply andb_prop in Ho as [Ho _]. apply andb_prop in Ho as [_ Hcov].
    destruct (find_cov L (ob_base o) lo) eqn:Hf; [|discriminate].
    clear -Ec Hf. revert Ec Hf. generalize 0%nat. induction L as [|o1 L1 IH]; cbn [find_cov find_cov_idx]; intros n Ec Hf; [discriminate|].
    destruct (covers_b o1 (ob_base o) lo); [discriminate | exact (IH _ Ec Hf)].
Qed.

End Sound.

Theorem mem_match_reshape : ltac2:(tb__ "0|1|
S18S63S8S15A1M0G0SfS4S71R2R1A2S7A3S2aVsegs;R4A2S2eVsegs;R6R4R5A4S2eVsegs;S66R7R5R6A3R4R6A4F_;F_;F_;FT;FL;Fms;Frho;").
Proof.
  intros rho ms L T H Hrom (Hall & Hpd & Hfr). unfold reshape_ok in H. apply andb_prop in H as [HT HP].
  split; [|split].
  - apply Forall_forall. intros o Hin. apply obj_holds_absorb. exact (objT_ok_sound rho ms L Hall Hrom o (proj1 (forallb_forall _ _) HT o Hin)).
  - apply pairwise_disjoint_absorb. exact (pairwise_sound rho L T HT Hpd HP).
  - intros a Ha. apply outside_all_absorb in Ha. unfold rho_absorb. cbn [rm].
    destruct (in_ranges_dec rho L a) as [Hin|Hnin]; [reflexivity|].
    apply Hfr. unfold outside_all. apply Forall_forall. intros o Hino. cbn beta. intros Hr. apply Hnin. exists o. split; [exact Hino | exact Hr].
Qed.

Theorem smatch_reshape : ltac2:(tb__ "0|1|
S18S3eS8S15A1S8S7aA1M0S63S79SfS4S71S32R5A1R4A2S7A3SfS4S3fS76R6R5A2A1S7A3S31Vsegs;R8R7SeG0S74R5S75R4R3A2A4A4S31Vsegs;S66R9S32R8A1R5A3S76R8R7A2SeG0S74R6S75R5R4A2A4A4F_;F_;F_;Fmd;Fms;Ftr;FT;FS;Frho;").
Proof.
  intros rho S T tr ms md H Hwf Hsm.
  destruct Hsm as (_ & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  unfold smatch. cbn [fst snd cfg_ms cfg_model set_objs ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
  split; [exact Hwf|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hroc|].
  split; [intros r Hr; unfold reg_sv; cbn [ss_regs]; rewrite eval_absorb; apply Hregs; exact Hr|].
  split; [intros r; unfold freg_sv; cbn [ss_fregs]; rewrite eval_absorb; apply Hfregs|].
  split; [destruct (ss_fcsr S); cbn in *; rewrite ?eval_absorb; exact Hfcsr|].
  split; [unfold resv_match in *; destruct (ss_resv S); destruct (ms_resv ms); rewrite ?eval_absorb; exact Hresv|].
  split; [exact (mem_match_reshape rho ms (ss_objs S) T H Hrom Hmem)|].
  apply Forall_forall. intros p Hp. apply holds_absorb. exact (proj1 (Forall_forall _ _) Hfacts p Hp).
Qed.

Lemma rm_reshape_outside : ltac2:(tb__ "0|0|
S18S8S15A1S63S4eQ40A1S13S67R4R3R1A3A1SfS3S4eQ8A1A1S25S66R5R4R3A3R2A2S25R5R2A2A3F_;Fa;Fms;FL;Frho;").
Proof. intros rho L ms a H. unfold rho_absorb. cbn [rm]. destruct (in_ranges_dec rho L a); [contradiction | reflexivity]. Qed.
Lemma rm_reshape_inside : ltac2:(tb__ "0|0|
S18S8S15A1S63S4eQ40A1S67R4R3R1A3SfS3S4eQ8A1A1S25S66R5R4R3A3R2A2S64R3R2A2A3F_;Fa;Fms;FL;Frho;").
Proof. intros rho L ms a H. unfold rho_absorb. cbn [rm]. destruct (in_ranges_dec rho L a); [reflexivity | contradiction]. Qed.
Lemma rw_reshape : ltac2:(tb__ "0|0|
S18S8S15A1S63S1SfS4eQ40A1S30S66R4R3R2A3R1A2S30R4R1A2A3Fi;Fms;FL;Frho;"). Proof. reflexivity. Qed.
Lemma rl_reshape : ltac2:(tb__ "0|0|
S18S8S15A1S63S1SfS8S4eQ8A1A1S2fS66R4R3R2A3R1A2S2fR4R1A2A3Fl;Fms;FL;Frho;"). Proof. reflexivity. Qed.

Definition fview (m : word -> option byte) (a : word) : option byte := ltac2:(tb__ "0|2|
S3S4eQ8A1M0A1M1G1Lx;Vm;Va;A1G0S6G0R1A2Lb;S23Vsegs;Va;A2X3x2").

Lemma fview_reshape_inside : ltac2:(tb__ "0|0|
S18S8S15A1S63S4eQ40A1S2aVsegs;R2A2S67R5R4R2A3SfS3S4eQ8A1A1S6fS25S66R6R5R4A3A1R3A2S21R4R3A2A3F_;F_;Fa;Fms;FL;Frho;").
Proof.
  intros rho L ms a Hrom Hin. unfold fview. rewrite (rm_reshape_inside rho L ms a Hin). unfold rd, ms_read_byte. rewrite (Hrom a). reflexivity.
Qed.

Theorem reshape_byte : ltac2:(tb__ "0|9|
S18S63S8S15A1S15S0S0S0S73S15S1dVsegs;R7R6A3R5A3S2aVsegs;R7A2S60S15R6R7A3SfS3S0A1M0S40S1aR7A1A1S6S0R6A2M1A3SfG0S40S19R8A1A1G1A3S10S53R8R6A2S54R6R7A2A2S4fQ40M2S51S50G2S1cRdS1bRaA1A2A2R7A2A2S4eG2A1M3S25S66ReRcRdA3A1G3S3S4eQ8M4A1M5A1M6F_;S10S11G5G5SfG6S6fR2R3A2M7S6G5R1A2M8A3Lb;A2S41OLx;S48RcR9A2S12S12S0SfG6G7S6G5S4fG4R1A2A2A3Lv;S10SfG6R1R2A1ScG5A1A3S11G5G5SfG6S23Vsegs;R3A2G8A3Lb;A2A2X41x4A2Tm;Ta;F_;F_;F_;F_;F_;F_;Foff;Fhi;Flo;Fo;FL;Fms;Frho;").
Proof.
  intros rho ms L o lo hi off HL Hrom Hin Hlo Hhi Hoff a m.
  pose proof (proj1 (Forall_forall _ _) HL o Hin) as Ho.
  pose proof (obj_byte_sound rho ms Hrom o lo hi off Ho Hlo Hhi Hoff) as [X1 X2].
  assert (IN : in_ranges rho L a).
  { exists o. split; [exact Hin|]. pose proof Ho as (Hb & _). unfold obj_range, obj_lo_of, obj_hi_of in *. cbn [fst snd].
    rewrite (soff_small rho _ _ Hlo), (soff_small rho _ _ Hhi) in *. subst a. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite U64; lia). lia. }
  subst m. rewrite (fview_reshape_inside rho L ms a Hrom IN). split; [exact X1|].
  destruct (obj_byte o off); try exact I; [exact X2|]. rewrite (rm_reshape_inside rho L ms a IN). exact X2.
Qed.
End Check.
