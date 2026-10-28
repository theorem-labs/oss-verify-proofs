(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_platform_zeroize.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_asn1_get_len.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_asn1_get_alg_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac.
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

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

Local Ltac zero_call parv lov csp :=
  lxp_gc; try lxp_statics;
  lazymatch goal with H : rw_cells _ _ parv _ |- _ =>
    let junk := fresh "junk" in let H' := fresh "HPZ" in
    destruct (rw_cells_forget _ _ _ _ H) as [junk H']; clear H;
    cbn [cells_size csize Nat.add] in H' end;
  lazymatch goal with HZ0 : platform_zeroize_stmt _ _ _ _ |- _ =>
    let SPZ := fresh "SPZ" in
    pose proof HZ0 as SPZ; unfold platform_zeroize_stmt, U_PLATFORM_ZEROIZE in SPZ;
    callx_sp csp
      (eapply SPZ with (A := parv) (n := 24) (lo := lov); rewrite ?(unsigned_lit csp) by plia;
       try eassumption; try reflexivity; try plia);
    clear SPZ end;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with H : rw_cells _ mx parv _ |- _ =>
      cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.mul repeat] in H;
      apply (rw_cells_zeros usegs mx parv 24 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) in H;
      [| cbn; repeat split; reflexivity | reflexivity] end end;
  lxp_gc.

Local Ltac split_len_cell rec :=
  lazymatch goal with H : rw_cells _ _ rec _ |- _ =>
    let H0 := fresh "HC" in let H1 := fresh "HC" in let H2 := fresh "HC" in let H3 := fresh "HC" in
    lxp_chunk_split H 2%nat H0 H1; lxp_chunk_split H1 1%nat H2 H3 end.

Local Ltac run_u := lxp_run (PLAN [0x1e4e4; 0x259d4; 0x1ef88] [] 200%N).

Local Ltac zero_post :=
  lazymatch goal with |- 0 = 0 -> exists _ _, _ => idtac end;
  intros _; eexists _, 0; split; [reflexivity|]; split; [reflexivity|]; split; [plia|]; split; [plia|];
  left; rewrite ?unsigned_lit by plia; repeat split; first [plia | reflexivity].

Local Ltac succ_post :=
  lazymatch goal with |- 0 = 0 -> exists _ _, _ => idtac end;
  intros _; eexists _, _; split; [reflexivity|]; split; [reflexivity|];
  bvu_ranges; split; [plia|]; split; [plia|]; right; split; plia.

Section Walk.
  Variable L : heap_layout.
  Hypothesis HZ : platform_zeroize_stmt usegs L U_PLATFORM_ZEROIZE U_MEMSET_FUNC.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP ALG PAR P END BUF lo : Z) (bs : list byte).
  Hypothesis B1 : BUF <= P.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= ALG \/ ALG + 24 <= PP.
  Hypothesis D1b : PP + 8 <= PAR \/ PAR + 24 <= PP.
  Hypothesis D1c : ALG + 24 <= PAR \/ PAR + 24 <= ALG.
  Hypothesis D2 : PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D3 : ALG + 24 <= BUF \/ BUF + Z.of_nat (length bs) <= ALG.
  Hypothesis D3b : PAR + 24 <= BUF \/ BUF + Z.of_nat (length bs) <= PAR.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis AL2 : ALG mod 8 = 0.
  Hypothesis AL3 : PAR mod 8 = 0.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis ALGB : 0 <= ALG /\ ALG + 24 <= 2^64.
  Hypothesis PARB : 0 <= PAR /\ PAR + 24 <= 2^64.
  Hypothesis BUF0 : 0 <= BUF.
  Hypothesis NZ1 : 0 < PP.
  Hypothesis NZ2 : 0 < ALG.
  Hypothesis NZ3 : 0 < PAR.
  Hypothesis NZ4 : 0 < BUF.
  Hypothesis SLO : lo <= bv_unsigned sp - 64.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis ACP : 4096 < alloc_ceiling.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : ALG + 24 <= lo \/ bv_unsigned sp <= ALG.
  Hypothesis DS3 : PAR + 24 <= lo \/ bv_unsigned sp <= PAR.
  Hypothesis DS4 : BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis CA : const_at L U_MEMSET_FUNC 8.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis OD1 : PP + 8 <= hl_data_lo L \/ hl_data_hi L <= PP.
  Hypothesis OD2 : ALG + 24 <= hl_data_lo L \/ hl_data_hi L <= ALG.
  Hypothesis OD3 : PAR + 24 <= hl_data_lo L \/ hl_data_hi L <= PAR.
  Hypothesis SPB : bv_unsigned sp < 2^64.

  Notation W := [(PP, PP + 8); (ALG, ALG + 24); (PAR, PAR + 24); (bv_unsigned sp - ASN1_GET_ALG_STACK, bv_unsigned sp)].
  Notation POST := (asn1_get_alg_post usegs L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP ALG PAR P END BUF lo m).

  (* [comment removed for export] *)
  Lemma main_walk : forall (atag apad alen apw ptag ppad plen ppw x5 x6 x7 x14 x15 x16 x17 : word),
    P <= END ->
    rw_cells usegs m PP [C8 (Z_to_bv 64 P)] ->
    rw_cells usegs m ALG [C4 atag; C4 apad; C8 alen; C8 apw] ->
    rw_cells usegs m PAR [C4 ptag; C4 ppad; C8 plen; C8 ppw] ->
    bytes_at usegs m BUF bs -> stk usegs m lo (bv_unsigned sp) -> statics_ok usegs L m -> mem_inv usegs m ->
    evt usegs POST
      (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 PP) (Z_to_bv 64 END) (Z_to_bv 64 ALG) (Z_to_bv 64 PAR) x14
              x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 U_ASN1_GET_ALG) fc None m (seg_rom usegs)).
  Proof.
  intros atag apad alen apw ptag ppad plen ppw x5 x6 x7 x14 x15 x16 x17 B2 HPP HALG HPAR HBUF ST SOK MI.
  unfold U_ASN1_GET_ALG.
  pose proof (munch_refl W m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (proj1 ST) as LO0.
  carve_frame 48%nat ST.
  lxp_split_frame [8;8;8;8;8;8]%nat. lxp_seps 48.
  run_u.
  all: try lxp_ret.
  lxp_gc. try lxp_statics.
  lxp_cells FR.
  lxp_chunk_split FR 1%nat FL FR.
  call_len U_asn1_get_len_spec PP BUF bs (bv_unsigned sp + -48) (bv_unsigned sp + -48).
  all: run_u.
  all: try lxp_ret.
  lxp_gc. try lxp_statics.
  split_len_cell ALG.
  call_len U_asn1_get_len_spec PP BUF bs (ALG + 8) (bv_unsigned sp + -48).
  all: run_u.
  all: try lxp_ret.
  all: first [ lxp_at 154068; zero_call PAR lo (bv_unsigned sp + -48); run_u; lxp_ret; zero_post
             | lxp_at 124132; lxp_gc; try lxp_statics; split_len_cell PAR;
               call_len U_asn1_get_len_spec PP BUF bs (PAR + 8) (bv_unsigned sp + -48);
               run_u; lxp_ret ].
  all: try (bvu_ranges; plia).
  all: try succ_post.
Qed.
End Walk.

Lemma U_asn1_get_alg_spec : forall L, platform_zeroize_stmt usegs L U_PLATFORM_ZEROIZE U_MEMSET_FUNC ->
  asn1_get_alg_stmt usegs L U_ASN1_GET_ALG U_MEMSET_FUNC.
Proof.
  intros L HZ. unfold asn1_get_alg_stmt.
  intros until ppw. intros HPP HALG HPAR HBUF B1 B2 B3 B4 D1 D1b D1c D2 D3 D3b AL1 AL2 AL3 NZ1 NZ2 NZ3 NZ4 ST SLO ACL SPA DS1 DS2 DS3 DS4
         SOK CA DHI OD1 OD2 OD3 MI -> -> -> ->.
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB. pose proof (rw_cells_bound _ _ _ _ HALG) as ALGB. pose proof (rw_cells_bound _ _ _ _ HPAR) as PARB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in PPB, ALGB, PARB.
  pose proof (proj1 HBUF) as BUF0. pose proof alloc_ceiling_pos as ACP.
  pose proof (bv_unsigned_in_range 64 sp) as SPB. unfold bv_modulus in SPB. cbn in SPB.
  eapply main_walk; try eassumption; try nia.
Qed.
