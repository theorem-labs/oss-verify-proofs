(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_asn1_get_len.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_asn1_get_bitstring () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "bitstring_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "asn1_get_bitstring_post"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.to_nat"].


Definition U_ASN1_GET_BITSTRING : Z := 0x1e90c.

(* [comment removed for export] *)
Notation ASN1_GET_BITSTRING_STACK := 32 (only parsing).

Definition bitstring_cells (len : word) (ub : byte) (pad : list byte) (p : word) : list cell :=
  [C8 len; C1 ub; CB 7 pad; C8 p].

Definition asn1_get_bitstring_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PP BSP P END BUF lo : Z) (pad : list byte) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_bitstring ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lr,$4.(1.$4.Lp',$4.(1.(2.&40.)LL,(2.&40.)(1.(2.&8.)Lub,(2.&8.)(1.(2.&40.)Lpw,(2.&40.)(5.(6.$0.R16.(7.(8.O1:.O19.O18.O17.R15.R14.R13.O16.O15.R12.R11.R10.R?.R>.R=.R<.R;.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.R:.R9.R8.R7.)O:.(9.O1:.)O9.(:.(2.&40.))R6.(;.O1;.)))(5.(<.(=.(>.$4.$4.)(?.$4.$4.O8.(10.O8.+8.))(=.(>.$4.$4.)(?.$4.$4.O7.(10.O7.+18.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.O19.)+20.)(12.&40.O19.))(13.(>.$4.$4.)))))O1.R6.)(5.(14.O1;.O1.R6.)(5.(15.O1;.R6.)(5.(6.(2.&40.)R12.(16.&40.R5.))(5.(5.(17.-7?.R5.)(18.R5.=))(5.(19.O1;.R6.O8.(=.$1:.(1;.(16.&40.R4.))(13.$1:.)))(5.(19.O1;.R6.O7.(1<.R3.R2.O2.R1.))(5.(1=.O1;.R6.O3.(12.&40.O19.))(5.(5.(18.O6.R4.)(18.R4.O5.))P,(6.$4.R5.=)(1.$4.Lq,$4.(5.(6.(2.&40.)R3.(16.&40.R1.))(5.(18.(10.O6.+3.)R1.)(5.(6.$4.(10.R1.(12.&40.R5.))R6.)(6.$4.R6.O5.))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition asn1_get_bitstring_stmt {L : heap_layout} (segs : list Segment) (ENTRY : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (PP BSP P END BUF lo : Z) (bs : list byte) (lenv : word) (ubv : byte) (pad : list byte) (pv : word),
  rw_cells segs m PP [C8 (Z_to_bv 64 P)] ->
  rw_cells segs m BSP (bitstring_cells lenv ubv pad pv) ->
  bytes_at segs m BUF bs ->
  BUF <= P -> P <= END -> END <= BUF + Z.of_nat (length bs) -> BUF + Z.of_nat (length bs) < 2^63 ->
  (PP + 8 <= BSP \/ BSP + 24 <= PP) ->
  (PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP) ->
  (BSP + 24 <= BUF \/ BUF + Z.of_nat (length bs) <= BSP) ->
  (* [comment removed for export] *)
  PP mod 8 = 0 -> BSP mod 8 = 0 -> 0 < PP -> 0 < BSP -> 0 < BUF ->
  (* [comment removed for export] *)
  stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ASN1_GET_BITSTRING_STACK -> alloc_ceiling <= lo ->
  bv_unsigned sp mod 16 = 0 ->
  (PP + 8 <= lo \/ bv_unsigned sp <= PP) ->
  (BSP + 24 <= lo \/ bv_unsigned sp <= BSP) ->
  (BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF) ->
  mem_inv segs m ->
  a0 = Z_to_bv 64 PP -> a1 = Z_to_bv 64 END -> a2 = Z_to_bv 64 BSP ->
  evt segs (asn1_get_bitstring_post segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP BSP P END BUF lo pad m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).

Local Ltac len_post :=
  repeat match goal with H : ?x = Z_to_bv 64 _ |- _ => is_var x; subst x end;
  match goal with HR : ?r = 0 -> _, HB : -127 < ?r <= 0 |- _ =>
    let a := fresh "HR" in let b := fresh "HR" in let rn := fresh "RN" in
    destruct (Z.eq_dec r 0) as [R0|R0];
    [ subst r; specialize (HR eq_refl); destruct HR as [a b]
    | assert (rn : r <= -1) by lia; clear HR R0 ] end.
Local Ltac bvu_ranges :=
  repeat match goal with
  | H : context [bv_unsigned ?w] |- _ => is_var w;
      lazymatch goal with _ : 0 <= bv_unsigned w < _ |- _ => fail | _ => pose proof (bv_unsigned_in_range 64 w) end
  | |- context [bv_unsigned ?w] => is_var w;
      lazymatch goal with _ : 0 <= bv_unsigned w < _ |- _ => fail | _ => pose proof (bv_unsigned_in_range 64 w) end
  end.
Local Ltac call_len spec ppv bufv bsv lenp csp :=
  lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?e) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
  lazymatch goal with H : rw_cells _ _ ppv [C8 (Z_to_bv 64 ?p)] |- _ =>
    let SP := fresh "SP" in
    pose proof spec as SP; unfold asn1_get_len_stmt, U_ASN1_GET_LEN in SP;
    callx_sp csp
      (eapply SP with (PP := ppv) (LENP := lenp) (P := p) (END := e) (BUF := bufv) (bs := bsv);
       rewrite ?(unsigned_lit csp) by plia; try eassumption; try reflexivity; try plia; try (bvu_ranges; plia));
    clear SP
  end end;
  len_post.
Local Ltac split_first rec :=
  lazymatch goal with H : rw_cells _ _ rec (_ :: _ :: _) |- _ =>
    let H1 := fresh "HBL" in let H2 := fresh "HBR" in lxp_chunk_split H 1%nat H1 H2 end.
Local Ltac run_b := lxp_run (PLAN [0x1e4e4; 0x1ea20] [] 240%N).

Lemma U_asn1_get_bitstring_spec {L : heap_layout} : asn1_get_bitstring_stmt usegs U_ASN1_GET_BITSTRING.
Proof.
  (* [comment removed for export] *)
  unfold asn1_get_bitstring_stmt, U_ASN1_GET_BITSTRING.
  intros until pv.
  intros HPP HBS HBUF B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 ST SLO ACL SPA DS1 DS2 DS3 MI -> -> ->.
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB.
  pose proof (rw_cells_bound _ _ _ _ HBS) as BSB.
  cbn [bitstring_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in PPB, BSB.
  pose proof (proj1 HBUF) as BUF0.
  pose proof (munch_refl [(PP, PP + 8); (BSP, BSP + 24); (bv_unsigned sp - ASN1_GET_BITSTRING_STACK, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (@alloc_ceiling_pos L) as ACP.
  pose proof (bv_unsigned_in_range 64 sp) as SPB. unfold bv_modulus in SPB. cbn in SPB.
  pose proof (proj1 ST) as LO0.
  unfold bitstring_cells in HBS.
  carve_frame 32%nat ST.
  lxp_split_frame [8;8;8;8]%nat.
  run_b.
  (* [comment removed for export] *)
  all: try lxp_ret.
  lxp_gc. try lxp_statics.
  split_first BSP.
  call_len U_asn1_get_len_spec PP BUF bs BSP (bv_unsigned sp + -32).
  all: bvu_ranges.
  all: run_b.
  all: lxp_ret.
Qed.

