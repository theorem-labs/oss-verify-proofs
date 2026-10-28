From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux AStep CellsX HeapIface Image Asn1AuxA X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_asn1_get_sequence_of_A U_asn1_get_sequence_of.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPHeap.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat2.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition U_X509_CRT_EXT_SEQ : Z := 0x2722c.

Definition crt_ext_seq_ret (r cp : Z) : Z :=
  if Z.eqb r 0 then (if Z.eqb cp 0 then -9572 else 0) else r - 9472.

Definition crt_ext_seq_post (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : HST segs L HI) (LB : list blk) (PP CUR P END BUF lo : Z) (m : mem) (mo : Model) : config -> Prop :=
  fun c => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (mo' : Model) (h' : HST segs L HI)
                  (r p' : Z) (ct cpad : word) (cl cp cn : Z) (nodes : list Z),
    c = mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom segs)) mo' /\
    mem_inv segs m' /\
    stk segs m' lo (bv_unsigned sp) /\
    mo_frame mo mo' /\
    heap_top segs L HI h' = heap_top segs L HI h /\
    a0 = Z_to_bv 64 (crt_ext_seq_ret r cp) /\
    (-127 < r /\ r <= 0) /\
    rw_cells segs m' PP [C8 (Z_to_bv 64 p')] /\
    (P <= p' /\ p' <= END) /\
    rw_cells segs m' CUR (seq_cells ct cpad cl cp cn) /\
    ((cp = 0 /\ cl = 0 /\ nodes = []) \/ (BUF <= cp /\ 0 <= cl /\ cp + cl <= END)) /\
    cn = hd 0 nodes /\
    seq_chain segs (fun _ : list cell => True) m' (map (fun a => (a, 32)) (rev nodes) ++ LB) cn nodes /\
    List.NoDup nodes /\
    (forall x, In x nodes -> forall B k, In (B, k) LB -> x + 32 <= B \/ B + k <= x) /\
    HEAP segs L HI h' (map (fun a => (a, 32)) (rev nodes) ++ LB) m' mo' /\
    heap_presx segs L LB (bv_unsigned sp) [(PP, PP + 8); (CUR, CUR + 32)] m m'.

Definition crt_ext_seq_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (h : HST segs L HI) (LB : list blk)
         (PP CUR P END BUF lo : Z) (bs cjunk : list byte),
  HEAP segs L HI h LB m mo ->
  rw_cells segs m PP [C8 (Z_to_bv 64 P)] ->
  rw_cells segs m CUR [CB 32 cjunk] ->
  bytes_at segs m BUF bs ->
  BUF <= P -> P <= END -> END <= BUF + Z.of_nat (length bs) -> BUF + Z.of_nat (length bs) < 2 ^ 63 ->
  (PP + 8 <= CUR \/ CUR + 32 <= PP) ->
  (PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP) ->
  (CUR + 32 <= BUF \/ BUF + Z.of_nat (length bs) <= CUR) ->
  PP mod 8 = 0 -> CUR mod 8 = 0 -> 0 < PP -> 0 < CUR -> 0 < BUF ->
  stk segs m lo (bv_unsigned sp) ->
  lo <= bv_unsigned sp - 192 - hl_stack L ->
  alloc_ceiling <= lo ->
  bv_unsigned sp <= heap_top segs L HI h ->
  bv_unsigned sp mod 16 = 0 ->
  hl_data_hi L <= alloc_ceiling ->
  hl_img_lo L <= hl_data_lo L ->
  hl_data_hi L <= hl_img_hi L ->
  (PP + 8 <= lo \/ bv_unsigned sp <= PP) ->
  (CUR + 32 <= lo \/ bv_unsigned sp <= CUR) ->
  (BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF) ->
  client_wrange L LB lo (heap_top segs L HI h) PP 8 ->
  client_wrange L LB lo (heap_top segs L HI h) CUR 32 ->
  client_range L LB lo BUF (Z.of_nat (length bs)) ->
  tp = Z_to_bv 64 (hl_tp L) ->
  mem_inv segs m ->
  a0 = Z_to_bv 64 PP -> a1 = Z_to_bv 64 END -> a2 = Z_to_bv 64 CUR ->
  aevtM segs mo (crt_ext_seq_post segs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB PP CUR P END BUF lo m mo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).

Section Walk.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HSEQ : asn1_get_sequence_of_stmt usegs L HI U_ASN1_GET_SEQUENCE_OF.
  Hypothesis HLS : 0 <= hl_stack L.

  Ltac fin_run :=
    lxp_gc;
    lxp_run (PLAN [0x27290] [] 40%N);
    lxp_ret_open; apply aevtM_done; unfold crt_ext_seq_post; flexi 15%nat.
  Ltac fin_rest :=
    first [ assumption
          | f_equal; unfold crt_ext_seq_ret;
            repeat (match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b) end); lia ].

  Lemma crt_ext_seq_walk : crt_ext_seq_stmt usegs L HI U_X509_CRT_EXT_SEQ.
  Proof.
  unfold crt_ext_seq_stmt, U_X509_CRT_EXT_SEQ.
  intros until cjunk.
  intros HH HPP HCUR HBUF B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 ST SLO ACL HTOP SPA DHI DIM1 DIM2 DS1 DS2 DS3
    CWPP CWCUR CRBUF TP MI -> -> ->.
  pose proof alloc_ceiling_pos as ACP.
  pose proof (bv_unsigned_in_range 64 sp) as SPR.
  try (unfold bv_modulus in SPR).
  try (cbn in SPR).
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB.
  pose proof (rw_cells_bound _ _ _ _ HCUR) as CURB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PPB, CURB.
  change (Z.of_nat 8) with 8 in PPB.
  change (Z.of_nat 32) with 32 in CURB.
  pose proof (bytes_at_bound _ _ _ _ HBUF) as BB.
  flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR0 _.
  pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
  pose proof (conj HH I) as HHbox.
  pose proof (munch_refl [(PP, PP + 8); (bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  carve_frame 16%nat ST.
  lxp_split_frame [8;8]%nat.
  try (pose proof (heap_presx_refl usegs L LB (bv_unsigned sp) [(PP, PP + 8); (CUR, CUR + 32)] m) as HPX0).
  lxp_run (PLAN [0x1ecc4; 0x27290] [] 40%N).
  lxp_gc. try lxp_statics.
  pose proof HSEQ as SPE.
  unfold asn1_get_sequence_of_stmt, U_ASN1_GET_SEQUENCE_OF in SPE.
  eapply aevtM_cut; [ eapply SPE with (PP := PP) (CUR := CUR) (P := P) (END := END) (BUF := BUF) (bs := bs) (lo := lo) (LB := LB) (h := h) (tag := 6);
    rewrite ?(unsigned_lit (bv_unsigned sp + -16)) by dlia; lxp_reg_refl; try eassumption; try reflexivity; try flia2 | ].
  try clear SPE.
  intros ms' mo' PO.
  unfold asn1_get_sequence_of_post in PO.
  destruct_exs PO.
  flat constr:(PO) 2%nat. flclear PO. intros E PO.
  injection E as E1 E2.
  subst ms' mo'.
  try (rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in PO by dlia).
  flat constr:(PO) 16%nat. flclear PO. intros MI6 ST6 MF6 HT6 Ha0 Hr6 HPP6 Hp6 HCUR6 HCB6 Hcn HCH6 HND6 HAP6 HH6 HPX6.
  lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
    replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
  lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m6; rename mox into mo6 end.
  match type of HH6 with HEAP _ _ _ ?hh _ _ _ => rename hh into h6 end.
  match type of Ha0 with ?x = Z_to_bv 64 ?rr => subst x; rename rr into r end.
  match type of HPP6 with rw_cells _ _ _ [C8 (Z_to_bv 64 ?p)] => rename p into pq end.
  match type of HCUR6 with rw_cells _ _ _ (seq_cells ?a ?b ?c ?d ?e) =>
    rename a into ct; rename b into cpad; rename c into cl; rename d into cp; rename e into cn end.
  match type of HND6 with List.NoDup ?n => rename n into nodes end.
  pose proof (heap_mok _ _ HI _ _ _ _ HH6) as MK6.
  lxp_after_call.
  try clear MK.
  try clear MU. try clear WM. try clear HBUF. try clear HPP. try clear HCUR. try clear HPX0.
  unfold seq_cells in HCUR6.
  destruct (Z.eq_dec r 0) as [Hr0|Hr0].
  - subst r.
    pose proof HCB6 as HCBc.
    destruct HCBc as [(Hcp & Hcl & Hnd) | (Hcp1 & Hcl1 & Hcp2)].
    + subst cp. fin_run.
      exists m6, mo6, h6, 0, pq, ct, cpad, cl, 0, cn, nodes.
      split; [reflexivity|]. lxp_ret_close. all: fin_rest.
    + assert (CPP : 0 < cp) by lia. fin_run.
      exists m6, mo6, h6, 0, pq, ct, cpad, cl, cp, cn, nodes.
      split; [reflexivity|]. lxp_ret_close. all: fin_rest.
  - assert (RN : r < 0) by lia. fin_run.
    exists m6, mo6, h6, r, pq, ct, cpad, cl, cp, cn, nodes.
    split; [reflexivity|]. lxp_ret_close. all: fin_rest.
  Qed.
End Walk.

Lemma U_x509_crt_ext_seq_spec (L : heap_layout) (HI : heap_iface usegs L) :
  hl_calloc L = U_CALLOC -> 0 <= hl_stack L -> crt_ext_seq_stmt usegs L HI U_X509_CRT_EXT_SEQ.
Proof.
  intros HC HLS. apply crt_ext_seq_walk; [| exact HLS].
  apply U_asn1_get_sequence_of_spec; assumption.
Qed.
