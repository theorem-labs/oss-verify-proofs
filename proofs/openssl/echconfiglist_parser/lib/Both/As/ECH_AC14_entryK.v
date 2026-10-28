From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame SFModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C5 ECH_AStmt_C10 ECH_AStmt_C13 ECH_AKit ECH_AsKit ECH_AsKitK AsStack0.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_memchr N6_iface.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition BK_get2 : Z := 0x5546fc.
Definition BK_copy : Z := 0x5548cc.
Definition BK_get1 : Z := 0x554b88.
Definition BK_has0 : Z := 0x554d18.
Definition ADE_R2a : Z := 0x553ba8.
Definition ADE_R4a : Z := 0x553df4.
Definition ADE_R4b : Z := 0x553e2c.
Definition ADE_R5a : Z := 0x553e68.
Definition ADE_R4c : Z := 0x553e38.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac ck8m ACC a :=
    let ACx := fresh "ACx" in
    lazymatch type of ACC with accessible _ ?A ?n =>
    lazymatch goal with MUx : munch _ _ ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (ACx : accessible mc A n) by (eapply accessible_across; [exact ACC| exact MUx| repeat (apply Forall_cons; [cbn [fst snd]; unfold AHI_LO in *; lia|]); apply Forall_nil])
    end end; ck8_check ACx a; clear ACx.
  Local Ltac accm ACC ACx :=
    lazymatch type of ACC with accessible _ ?A ?n =>
    lazymatch goal with MUx : munch _ _ ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (ACx : accessible mc A n) by (eapply accessible_across; [exact ACC| exact MUx| repeat (apply Forall_cons; [cbn [fst snd]; unfold AHI_LO in *; lia|]); apply Forall_nil])
    end end.
  Local Ltac acfin AC := eapply ACONST_frame; [exact AC| eassumption| eassumption| repeat (apply Forall_cons; [first [eassumption| apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP, AHI_LO in *; rewrite ?ASHADOW_BASE_val; lia]|]); apply Forall_nil].
  Lemma apkK_byte : forall m base bs cur i b,
    bytes_at asegs m base bs -> nth_error bs (Z.to_nat (cur - base + i)) = Some b -> base <= cur -> 0 <= i ->
    ov_read_bytes asegs m (wa (cur + i)) 1 = Some [b].
  Proof.
    intros m base bs cur i b BS NTH LE I0. eapply (u8ro_read asegs m base bs (cur - base + i) b); [exact BS| exact NTH| lia|]. f_equal. lia.
  Qed.
  Local Ltac retpc0 := match goal with |- context [ret_pc (Z_to_bv 64 ?v)] => replace (ret_pc (Z_to_bv 64 v)) with (Z_to_bv 64 v) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
  Lemma shvis_acrossK : forall W m m' lo hi,
    shvis m lo hi -> munch W m m' -> wmono asegs m m' -> 0 <= lo -> lo <= hi <= AAPP_HI ->
    Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) W -> shvis m' lo hi.
  Proof.
    intros W m m' lo hi SV MU WM L0 LH HW. eapply shvis_transport; [exact SV| exact MU| exact WM|].
    pose proof (hull_lo_le lo L0) as (A1 & A2 & A3). pose proof (hull_hi_ge hi ltac:(lia)) as (B1 & B2 & B3).
    assert (S1 : ASHADOW_BASE <= sh (hull_lo lo)) by (unfold sh; Z.div_mod_to_equations; lia).
    assert (HH2 : hull_hi hi <= AAPP_HI) by (unfold hull_hi, AAPP_HI in *; Z.div_mod_to_equations; lia).
    assert (S2 : sh (hull_hi hi) <= AHI_LO) by (unfold sh, AHI_LO, AAPP_HI in *; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    rewrite ASHADOW_BASE_val in S1.
    clear - HW S1 S2. induction W as [|[l h] W IH]; [exact I|]. cbn. pose proof (Forall_inv HW) as K1. cbn in K1.
    split; [unfold ALOWSH_LO, AHI_LO in *; lia| exact (IH (Forall_inv_tail HW))].
  Qed.
  Lemma bytes_at_subK : forall m A zs i n,
    bytes_at asegs m A zs -> 0 <= i -> 0 <= n -> i + n <= Z.of_nat (length zs) ->
    bytes_at asegs m (A + i) (firstn (Z.to_nat n) (skipn (Z.to_nat i) zs)) /\ Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat i) zs))) = n.
  Proof.
    intros m A zs i n BS I0 N0 LE.
    rewrite <- (firstn_skipn (Z.to_nat i) zs) in BS. apply bytes_at_app in BS. destruct BS as [_ BS].
    rewrite firstn_length_le in BS by lia. rewrite Z2Nat.id in BS by lia.
    rewrite <- (firstn_skipn (Z.to_nat n) (skipn (Z.to_nat i) zs)) in BS. apply bytes_at_app in BS. destruct BS as [BS _].
    split; [exact BS|]. rewrite firstn_length_le; [lia|]. rewrite length_skipn. lia.
  Qed.

  Lemma bk_get2_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (P Q Bb cur ms rem lo blen : Z) (bs : list byte) (q0 q1 q2 : word),
      rw_cells asegs m P (pk_cells cur ms rem) -> rw_cells asegs m Q [C8 q0; C8 q1; C8 q2] -> P mod 8 = 0 -> Q mod 8 = 0 -> apart P 24 Q 24 ->
      bv_unsigned sp <= P -> bv_unsigned sp <= Q -> accessible m P 24 -> accessible m Q 24 ->
      bytes_at asegs m Bb bs -> Bb <= cur -> 0 <= rem -> cur + rem <= Bb + zlength bs -> 0 < Bb -> Bb + zlength bs <= aceil -> 0 <= ms < 2^64 ->
      accessible m Bb blen -> zlength bs <= blen ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned ra mod 2 = 0 -> mem_inv asegs m -> ACONST m ->
      evt asegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' rv,
          munch [(bv_unsigned sp + -16, bv_unsigned sp); (P, P + 24); (Q, Q + 24)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ ACONST m'
          /\ ( (rv = 0 /\ rw_cells asegs m' P (pk_cells cur ms rem) /\ rw_cells asegs m' Q [C8 q0; C8 q1; C8 q2])
             \/ (rv = 1 /\ exists len hi lb, 0 <= hi < 256 /\ 0 <= lb < 256 /\ len = lb + 256 * hi /\ 2 + len <= rem /\
                  nth_error bs (Z.to_nat (cur - Bb + 0)) = Some (Z_to_bv 8 hi) /\ nth_error bs (Z.to_nat (cur - Bb + 1)) = Some (Z_to_bv 8 lb) /\
                  rw_cells asegs m' P (pk_cells (cur + 2 + len) ms (rem - 2 - len)) /\ rw_cells asegs m' Q (pk_cells (cur + 2) ms len)) )
          /\ ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 rv) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (ret_pc ra) fc None m' (seg_rom asegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 Q) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 BK_get2) fc None m (seg_rom asegs)).
  Proof.
    intros until q2. intros PK QC ALP ALQ APQ SPP SPQ ACCP ACCQ BS BC R0 CR BP BH MSR ACCB BL ST CEIL LO RAE MI AC.
    unfold BK_get2, pk_cells, apart, wz in *. acb. pose proof (aword_range sp) as SPR. pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *.
    pose proof (rw_cells_bound _ _ _ _ PK) as PB. pose proof (rw_cells_bound _ _ _ _ QC) as QB. cbn [cells_size csize Nat.add] in PB, QB.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof ACCP as (_ & AHIP & _). pose proof ACCQ as (_ & AHIQ & _). pose proof ACCB as (_ & AHIB & _). unfold AAPP_HI in AHIP, AHIQ, AHIB.
    pose proof (munch_refl [(bv_unsigned sp + -16, bv_unsigned sp); (P, P + 24); (Q, Q + 24)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    destruct (ACONST_shbase m AC) as [GSB SHB0]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    carve_frame 16%nat ST.
    go.
    ck8m ACCP P.
    go.
    ck8m ACCP (P + 16).
    go.
    if_cases K0; zify_cond K0.
    - assert (R2 : rem < 2) by (revert K0; rewrite ?unsigned_lit by lia; intros K0; lia). clear K0.
      go. step.
      apply evt_done. do 14 eexists. match goal with MIx : mem_inv asegs ?mx |- _ => exists mx end. exists 0.
      lazymatch goal with FRx : rw_cells asegs ?mx (bv_unsigned sp + -16) _ |- _ => release_frame FRx ST (bv_unsigned sp) end.
      repeat match goal with |- _ /\ _ => split end; try eassumption; [ acfin AC | left; split; [reflexivity| split; assumption] | reflexivity].
    - assert (R2 : 2 <= rem) by (revert K0; rewrite ?unsigned_lit by lia; intros K0; lia). clear K0.
      go.
      accm ACCB ACB1.
      destruct (nth_error bs (Z.to_nat (cur - Bb + 0))) as [c0|] eqn:N0; [| apply nth_error_None in N0; lia].
      destruct (nth_error bs (Z.to_nat (cur - Bb + 1))) as [c1|] eqn:N1; [| apply nth_error_None in N1; lia].
      pose proof (byte_range c0) as C0R. pose proof (byte_range c1) as C1R.
      ck1_load ACB1 cur v1 V1 V2 Ha1.
      ck_K 6 0x554770 K1.
      { intros tv1. red_tset.
        go.
        ck1_load ACB1 (cur + 1) v2 V3 V4 Ha2.
        pose proof (apkK_byte _ _ _ _ _ _ BS N0 ltac:(lia) ltac:(lia)) as RD0.
        step. change (zxb c0) with (Z_to_bv 64 (bv_unsigned c0)).
        ck_K 28 0x554788 K2.
        { intros tv2. red_tset.
          pose proof (apkK_byte _ _ _ _ _ _ BS N1 ltac:(lia) ltac:(lia)) as RD1.
          go.
          change (zxb c1) with (Z_to_bv 64 (bv_unsigned c1)).
          rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (bv_unsigned c0 * 2 ^ 8)) by lia. rewrite (unsigned_lit (bv_unsigned c1)) by lia.
          replace (Z.lor (bv_unsigned c0 * 2 ^ 8) (bv_unsigned c1)) with (bv_unsigned c1 + 256 * bv_unsigned c0)
            by (rewrite Z.lor_comm; replace (bv_unsigned c0 * 2 ^ 8) with (Z.shiftl (bv_unsigned c0) 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity); rewrite (lor_shiftl8_add (bv_unsigned c1) (bv_unsigned c0)) by lia; lia).
          set (len := bv_unsigned c1 + 256 * bv_unsigned c0) in *. assert (LR : 0 <= len < 2^16) by (subst len; lia).
          if_cases K0; zify_cond K0.
          + assert (EN : 2 + len <= rem) by (revert K0; rewrite ?unsigned_lit by lia; intros K0; lia). clear K0.
            go. rewrite zb_lxor_ones by lia.
            go. ck8m ACCP P. go. ck8m ACCP (P + 16). go. ck8m ACCQ Q. go. ck8m ACCP (P + 8). go. ck8m ACCQ (Q + 8). go. ck8m ACCQ (Q + 16).
            go. step.
            apply evt_done. do 14 eexists. match goal with MIx : mem_inv asegs ?mx |- _ => exists mx end. exists 1.
            lazymatch goal with FRx : rw_cells asegs ?mx (bv_unsigned sp + -16) _ |- _ => release_frame FRx ST (bv_unsigned sp) end.
            repeat match goal with |- _ /\ _ => split end; try eassumption; [ acfin AC | | reflexivity].
            right. split; [reflexivity|]. exists len, (bv_unsigned c0), (bv_unsigned c1).
            repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity; try (clear - C0R C1R EN; subst len; lia).
            all: try (f_equal; symmetry; apply definitions.Z_to_bv_bv_unsigned).
            all: try (replace (rem + -2 - len) with (rem - 2 - len) by lia; assumption).
          + assert (EN : rem < 2 + len) by (revert K0; rewrite ?unsigned_lit by lia; intros K0; lia). clear K0.
            go. step.
            apply evt_done. do 14 eexists. match goal with MIx : mem_inv asegs ?mx |- _ => exists mx end. exists 0.
            lazymatch goal with FRx : rw_cells asegs ?mx (bv_unsigned sp + -16) _ |- _ => release_frame FRx ST (bv_unsigned sp) end.
            repeat match goal with |- _ /\ _ => split end; try eassumption; [ acfin AC | left; split; [reflexivity| split; assumption] | reflexivity]. }
        ck1_branch_blt (cur + 1) v2 V3 V4 Ha2 K2. }
      ck1_branch_blt cur v1 V1 V2 Ha1 K1.
    Unshelve. all: try exact (Z_to_bv 64 0); try exact 0.
  Qed.

  Lemma bk_copy_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (P D n Bb blen cur ms rem lo : Z) (bs junk : list byte),
      rw_cells asegs m P (pk_cells cur ms rem) -> P mod 8 = 0 -> bv_unsigned sp <= P -> accessible m P 24 ->
      rw_cells asegs m D [CB (Z.to_nat n) junk] -> (bv_unsigned sp <= D \/ D + n <= lo) -> aconst_ok (D, D + n) -> (D + n <= ALOWSH_LO \/ AHI_LO <= D) ->
      apart P 24 D n -> 1 <= n -> n <= 2^40 ->
      accessible m D n -> shvis m D (D + n) -> in_app_mem D (D + n) ->
      bytes_at asegs m Bb bs -> Bb <= cur -> 0 <= rem -> cur + rem <= Bb + zlength bs -> 0 < Bb -> Bb + zlength bs <= aceil ->
      accessible m Bb blen -> zlength bs <= blen -> shvis m Bb (Bb + zlength bs) -> in_app_mem Bb (Bb + zlength bs) -> (Bb + zlength bs <= D \/ D + n <= Bb) ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 4160 -> bv_unsigned ra mod 2 = 0 -> mem_inv asegs m -> ACONST m ->
      evt asegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' rv,
          munch [(bv_unsigned sp - 4160, bv_unsigned sp); (P, P + 24); (D, D + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ ACONST m'
          /\ ( (rv = 0 /\ rem < n /\ rw_cells asegs m' P (pk_cells cur ms rem) /\ rw_cells asegs m' D [CB (Z.to_nat n) junk])
             \/ (rv = 1 /\ n <= rem /\ rw_cells asegs m' P (pk_cells (cur + n) ms (rem - n)) /\ rw_cells asegs m' D [CB (Z.to_nat n) (firstn (Z.to_nat n) (skipn (Z.to_nat (cur - Bb)) bs))]) )
          /\ ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 rv) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (ret_pc ra) fc None m' (seg_rom asegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 D) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 BK_copy) fc None m (seg_rom asegs)).
  Proof.
    intros until junk. intros PK ALP SPP ACP DC SPD ACO WD APD N1 N40 ACD SVD IMD BS BC R0 CR BP BH ACB BL SVB IMB SDB ST CEIL LO RAE MI AC.
    unfold BK_copy, pk_cells, apart, wz in *. acb. pose proof (aword_range sp) as SPR. pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *.
    pose proof (rw_cells_bound _ _ _ _ PK) as PB. pose proof (rw_cells_bound _ _ _ _ DC) as DB. cbn [cells_size csize Nat.add] in PB, DB. rewrite Nat.add_0_r, Z2Nat.id in DB by lia.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof ACP as (_ & AHIP & _). pose proof ACD as (_ & AHID & _). pose proof ACB as (_ & AHIB & _). unfold AAPP_HI in AHIP, AHID, AHIB.
    pose proof (munch_refl [(bv_unsigned sp - 4160, bv_unsigned sp); (P, P + 24); (D, D + n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    destruct (ACONST_shbase m AC) as [GSB SHB0]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    carve_frame 64%nat ST.
    go.
    ck8m ACP (P + 16).
    go.
    if_cases K0; zify_cond K0.
    - assert (EN : n <= rem) by (revert K0; rewrite ?unsigned_lit by lia; intros K0; lia). clear K0.
      go.
      ck8m ACP P.
      go. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => match goal with BSx : bytes_at asegs mx Bb bs |- _ =>
        destruct (bytes_at_subK mx Bb bs (cur - Bb) n BSx ltac:(lia) ltac:(lia) ltac:(lia)) as [BSX XBL] end end.
      replace (Bb + (cur - Bb)) with cur in BSX by lia.
      accm ACB ACB0. accm ACD ACD0.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        assert (AC0 : ACONST mc) by (acfin AC);
        assert (SVB0 : shvis mc Bb (Bb + Z.of_nat (length bs))) by (eapply shvis_acrossK; [exact SVB| exact MU| exact WM| lia| unfold AAPP_HI; lia| repeat (apply Forall_cons; [cbn [fst snd]; unfold AHI_LO in *; lia|]); apply Forall_nil]);
        assert (SVD0 : shvis mc D (D + n)) by (eapply shvis_acrossK; [exact SVD| exact MU| exact WM| lia| unfold AAPP_HI; lia| repeat (apply Forall_cons; [cbn [fst snd]; unfold AHI_LO in *; lia|]); apply Forall_nil])
      end.
      pose proof asan_memcpy_ok as AMC. unfold asan_memcpy_stmt, amemcpy_stmt_at in AMC.
      eapply evt_cut; [eapply AMC with (src := firstn (Z.to_nat n) (skipn (Z.to_nat (cur - Bb)) bs)) (junk := junk) (lo := lo); rewrite ?unsigned_lit by lia;
        [ exact BSX| apply Nat2Z.inj; rewrite XBL, Z2Nat.id by lia; reflexivity| eassumption| lia
        | eapply accessible_sub; [exact ACB0| lia| lia| lia]| exact ACD0
        | eapply shvis_sub; [exact SVB0| lia| lia| lia| lia| lia]| exact SVD0
        | eassumption| exact CEIL| unfold AINTRIN_STACK; lia| eassumption| exact AC0| exact N40
        | eapply in_app_mem_sub; [exact IMB| lia| lia]| exact IMD
        | exact ACO
        | lia| left; lia]|].
      cbv beta. intros ms1 PO. unfold amemcpy_post in PO.
      destruct PO as (z0 & z1 & z2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & z3 & z4 & z5 & z6 & mh & -> & MUh & WMh & MIh & STh & DSTh & SRCh & ACh).
      rewrite (unsigned_lit D) in MUh, DSTh by lia. rewrite (unsigned_lit n) in MUh, DSTh by lia. rewrite (unsigned_lit cur) in SRCh by lia.
      rewrite (unsigned_lit (bv_unsigned sp + -64)) in MUh, STh by lia. unfold AINTRIN_STACK in MUh.
      lazymatch goal with FRx : rw_cells asegs _ (bv_unsigned sp + -64) _ |- _ =>
        apply (rw_cells_transport asegs _ _ mh _ _ FRx) in MUh as FRh; [| exact WMh| cbn; lia] end.
      lazymatch goal with PKx : rw_cells asegs _ P _ |- _ =>
        apply (rw_cells_transport asegs _ _ mh _ _ PKx) in MUh as PKh; [| exact WMh| cbn; lia] end.
      assert (MU2 : munch [(bv_unsigned sp - 4160, bv_unsigned sp); (P, P + 24); (D, D + n)] m mh) by (eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MUh]]; intros x Hx; cbn in Hx |- *; lia).
      pose proof (wmono_trans asegs _ _ _ WM WMh) as WM2.
      clear MU WM MUh WMh. rename MU2 into MU. rename WM2 into WM.
      retpc0.
      go. ck8m ACP P. go. ck8m ACP (P + 16). go. step.
      apply evt_done. do 14 eexists. match goal with MIx : mem_inv asegs ?mx |- _ => exists mx end. exists 1.
      lazymatch goal with FRx : rw_cells asegs ?mx (bv_unsigned sp + -64) _ |- _ => release_frame FRx STh (bv_unsigned sp) end.
      repeat match goal with |- _ /\ _ => split end; try eassumption; [ acfin AC | | reflexivity].
      right. split; [reflexivity|]. split; [exact EN|].
      replace (cur + n) with (n + cur) by lia. replace (rem - n) with (rem + - n) by lia.
      split; assumption.
    - assert (EN : rem < n) by (revert K0; rewrite ?unsigned_lit by lia; intros K0; lia). clear K0.
      go. step.
      apply evt_done. do 14 eexists. match goal with MIx : mem_inv asegs ?mx |- _ => exists mx end. exists 0.
      lazymatch goal with FRx : rw_cells asegs ?mx (bv_unsigned sp + -64) _ |- _ => release_frame FRx ST (bv_unsigned sp) end.
      repeat match goal with |- _ /\ _ => split end; try eassumption; [ acfin AC | left; split; [reflexivity| split; [exact EN| split; assumption]] | reflexivity].
    Unshelve. all: try exact (Z_to_bv 64 0); try exact 0.
  Qed.

  Lemma bk_get1_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (P Q Bb cur ms rem lo blen : Z) (bs : list byte) (q0 q1 q2 : word),
      rw_cells asegs m P (pk_cells cur ms rem) -> rw_cells asegs m Q [C8 q0; C8 q1; C8 q2] -> P mod 8 = 0 -> Q mod 8 = 0 -> apart P 24 Q 24 ->
      bv_unsigned sp <= P -> bv_unsigned sp <= Q -> accessible m P 24 -> accessible m Q 24 ->
      bytes_at asegs m Bb bs -> Bb <= cur -> 0 <= rem -> cur + rem <= Bb + zlength bs -> 0 < Bb -> Bb + zlength bs <= aceil -> 0 <= ms < 2^64 ->
      accessible m Bb blen -> zlength bs <= blen ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned ra mod 2 = 0 -> mem_inv asegs m -> ACONST m ->
      evt asegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' rv,
          munch [(bv_unsigned sp + -16, bv_unsigned sp); (P, P + 24); (Q, Q + 24)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ ACONST m'
          /\ ( (rv = 0 /\ rw_cells asegs m' P (pk_cells cur ms rem) /\ rw_cells asegs m' Q [C8 q0; C8 q1; C8 q2])
             \/ (rv = 1 /\ exists len, 0 <= len < 256 /\ 1 + len <= rem /\ nth_error bs (Z.to_nat (cur - Bb + 0)) = Some (Z_to_bv 8 len) /\
                  rw_cells asegs m' P (pk_cells (cur + 1 + len) ms (rem - 1 - len)) /\ rw_cells asegs m' Q (pk_cells (cur + 1) ms len)) )
          /\ ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 rv) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (ret_pc ra) fc None m' (seg_rom asegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 Q) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 BK_get1) fc None m (seg_rom asegs)).
  Proof.
    intros until q2. intros PK QC ALP ALQ APQ SPP SPQ ACCP ACCQ BS BC R0 CR BP BH MSR ACCB BL ST CEIL LO RAE MI AC.
    unfold BK_get1, pk_cells, apart, wz in *. acb. pose proof (aword_range sp) as SPR. pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *.
    pose proof (rw_cells_bound _ _ _ _ PK) as PB. pose proof (rw_cells_bound _ _ _ _ QC) as QB. cbn [cells_size csize Nat.add] in PB, QB.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof ACCP as (_ & AHIP & _). pose proof ACCQ as (_ & AHIQ & _). pose proof ACCB as (_ & AHIB & _). unfold AAPP_HI in AHIP, AHIQ, AHIB.
    pose proof (munch_refl [(bv_unsigned sp + -16, bv_unsigned sp); (P, P + 24); (Q, Q + 24)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    destruct (ACONST_shbase m AC) as [GSB SHB0]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    carve_frame 16%nat ST.
    go.
    ck8m ACCP P.
    go.
    ck8m ACCP (P + 16).
    go.
    if_cases K0; zify_cond K0.
    - assert (R2 : rem = 0) by (revert K0; rewrite ?unsigned_lit by lia; intros K0; lia). clear K0.
      go. step.
      apply evt_done. do 14 eexists. match goal with MIx : mem_inv asegs ?mx |- _ => exists mx end. exists 0.
      lazymatch goal with FRx : rw_cells asegs ?mx (bv_unsigned sp + -16) _ |- _ => release_frame FRx ST (bv_unsigned sp) end.
      repeat match goal with |- _ /\ _ => split end; try eassumption; [ acfin AC | left; split; [reflexivity| split; assumption] | reflexivity].
    - assert (R2 : 1 <= rem) by (revert K0; rewrite ?unsigned_lit by lia; intros K0; lia). clear K0.
      go.
      accm ACCB ACB1.
      ck1_load ACB1 cur v1 V1 V2 Ha1.
      ck_K 6 0x554bf0 K1.
      { intros tv1. red_tset.
        destruct (nth_error bs (Z.to_nat (cur - Bb + 0))) as [c0|] eqn:N0; [| apply nth_error_None in N0; lia].
        pose proof (apkK_byte _ _ _ _ _ _ BS N0 ltac:(lia) ltac:(lia)) as RD0. pose proof (byte_range c0) as C0R.
        step. change (zxb c0) with (Z_to_bv 64 (bv_unsigned c0)).
        go.
        if_cases K0; zify_cond K0.
        + assert (EN : 1 + bv_unsigned c0 <= rem) by (revert K0; rewrite ?unsigned_lit by lia; intros K0; lia). clear K0.
          go. rewrite zb_lxor_ones by lia.
          go. ck8m ACCP P. go. ck8m ACCP (P + 16). go. ck8m ACCQ Q. go. ck8m ACCP (P + 8). go. ck8m ACCQ (Q + 8). go. ck8m ACCQ (Q + 16).
          go. step.
          apply evt_done. do 14 eexists. match goal with MIx : mem_inv asegs ?mx |- _ => exists mx end. exists 1.
          lazymatch goal with FRx : rw_cells asegs ?mx (bv_unsigned sp + -16) _ |- _ => release_frame FRx ST (bv_unsigned sp) end.
          repeat match goal with |- _ /\ _ => split end; try eassumption; [ acfin AC | | reflexivity].
          right. split; [reflexivity|]. exists (bv_unsigned c0).
          repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity; try (clear - C0R EN; lia).
          all: try (f_equal; symmetry; apply definitions.Z_to_bv_bv_unsigned).
          all: try (replace (rem + -1 - bv_unsigned c0) with (rem - 1 - bv_unsigned c0) by lia; assumption).
        + assert (EN : rem < 1 + bv_unsigned c0) by (revert K0; rewrite ?unsigned_lit by lia; intros K0; lia). clear K0.
          go. step.
          apply evt_done. do 14 eexists. match goal with MIx : mem_inv asegs ?mx |- _ => exists mx end. exists 0.
          lazymatch goal with FRx : rw_cells asegs ?mx (bv_unsigned sp + -16) _ |- _ => release_frame FRx ST (bv_unsigned sp) end.
          repeat match goal with |- _ /\ _ => split end; try eassumption; [ acfin AC | left; split; [reflexivity| split; assumption] | reflexivity]. }
      ck1_branch_blt cur v1 V1 V2 Ha1 K1.
    Unshelve. all: try exact (Z_to_bv 64 0); try exact 0.
  Qed.

  Lemma bk_has0_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (P cur ms rem lo : Z) (buf : list byte),
      rw_cells asegs m P (pk_cells cur ms rem) -> P mod 8 = 0 -> bv_unsigned sp <= P ->
      bytes_at asegs m cur buf -> zlength buf = rem -> rem <= 2^40 -> 0 < cur -> cur + rem <= aceil ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 16 - AINTRIN_STACK -> bv_unsigned ra mod 2 = 0 -> mem_inv asegs m ->
      accessible m P 24 -> accessible m cur rem -> shvis m cur (cur + rem) -> in_app_mem cur (cur + rem) -> ACONST m ->
      evt asegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
          munch [(bv_unsigned sp + -16 + -AINTRIN_STACK, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ ACONST m'
          /\ ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (if find_byte 0 buf then 1 else 0)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (ret_pc ra) fc None m' (seg_rom asegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 BK_has0) fc None m (seg_rom asegs)).
  Proof.
    intros until buf. intros PK ALP SPP BS BL RB CP CH ST CEIL LO RAE MI ACP ACB SVB IAB AC.
    unfold BK_has0, pk_cells, wz, AINTRIN_STACK in *. acb. unfold zlength in *.
    pose proof (aword_range sp) as SPR.
    pose proof (rw_cells_bound _ _ _ _ PK) as PB. cbn [cells_size csize Nat.add] in PB.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof ACP as (_ & AHIP & _). pose proof ACB as (_ & AHIB & _). unfold AAPP_HI in AHIP, AHIB.
    pose proof (munch_refl [(bv_unsigned sp + -16 + -4096, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat ST.
    go.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (AC1 : ACONST mc) by (eapply ACONST_frame; [exact AC| exact MU| exact WM| apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP, AHI_LO in *; rewrite ?ASHADOW_BASE_val; lia| apply Forall_nil]]);
      assert (ACP1 : accessible mc P 24) by (eapply accessible_across; [exact ACP| exact MU| apply Forall_cons; [cbn [fst snd]; right; unfold AHI_LO in *; lia| apply Forall_nil]]);
      assert (ACB1 : accessible mc cur rem) by (eapply accessible_across; [exact ACB| exact MU| apply Forall_cons; [cbn [fst snd]; right; unfold AHI_LO in *; lia| apply Forall_nil]]);
      assert (SVB1 : shvis mc cur (cur + rem)) by (eapply shvis_acrossK; [exact SVB| exact MU| exact WM| lia| unfold AAPP_HI; lia| apply Forall_cons; [cbn [fst snd]; right; unfold AHI_LO in *; lia| apply Forall_nil]])
    end.
    destruct (ACONST_shbase _ AC1) as [GSB SHB0].
    unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    go.
    ck8_check ACP1 P.
    go.
    ck8_check ACP1 (P + 16).
    go.
    step.
    eapply evt_cut; [eapply memchr_icpt0_ok with (buf := buf) (lo := lo); rewrite ?unsigned_lit by lia;
      [eassumption| exact BL| lia| lia| exact ACB1| exact SVB1| eassumption| exact CEIL| unfold AINTRIN_STACK; lia| eassumption| exact AC1| exact IAB| left; lia]|].
    cbv beta. intros ms1 PO. unfold amemchr_post in PO.
    destruct PO as (z0 & z1 & z2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & z3 & z4 & z5 & z6 & mh & -> & MUh & WMh & MIh & STh & BSh & ACh).
    rewrite (unsigned_lit 0) by lia. rewrite (unsigned_lit rem) by lia. rewrite (unsigned_lit cur) by lia. change (0 mod 256) with 0.
    rewrite (unsigned_lit (bv_unsigned sp + -16)) in MUh, STh by lia. unfold AINTRIN_STACK in MUh.
    lazymatch goal with FRx : rw_cells asegs _ (bv_unsigned sp + -16) _ |- _ =>
      apply (rw_cells_transport asegs _ _ mh _ _ FRx) in MUh as FRh; [| exact WMh| cbn; split; [lia| exact I]] end.
    assert (MU2 : munch [(bv_unsigned sp + -16 + -4096, bv_unsigned sp)] m mh) by (eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MUh]]; intros x Hx; cbn in Hx |- *; first [lia| destruct Hx as [Hx1 Hx2]; split; [lia| exact I]]).
    pose proof (wmono_trans asegs _ _ _ WM WMh) as WM2.
    clear MU WM. rename MU2 into MU. rename WM2 into WM.
    retpc0.
    step.
    rewrite v_sltu_b2z. rewrite (unsigned_lit 0) by lia.
    replace (Z_to_bv 64 (Z.b2z (0 <? bv_unsigned (Z_to_bv 64 (memchr_res cur 0 rem buf))))) with (Z_to_bv 64 (if find_byte 0 buf then 1 else 0)).
    2:{ unfold memchr_res. rewrite <- BL, Nat2Z.id, firstn_all. destruct (find_byte 0 buf) as [i|] eqn:FB.
        - pose proof (find_byte_Some _ _ _ FB) as (Hi & _). rewrite unsigned_lit by lia. destruct (Z.ltb_spec 0 (cur + Z.of_nat i)); [reflexivity| exfalso; lia].
        - rewrite unsigned_lit by lia. reflexivity. }
    go. step.
    apply evt_done. do 14 eexists. exists mh.
    lazymatch goal with FRx : rw_cells asegs ?mx (bv_unsigned sp + -16) _ |- _ => release_frame FRx STh (bv_unsigned sp) end.
    repeat match goal with |- _ /\ _ => split end; try eassumption. reflexivity.
  Qed.
End S.
