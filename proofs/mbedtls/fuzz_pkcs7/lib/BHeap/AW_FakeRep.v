(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AW_Poison HMLib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Dealloc AW_SFree5 AW_SMalloc AW_SMalloc1 AW_SMalloc2 AW_SMalloc3 AW_SMalloc4 AW_SMalloc5.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_FakeDefs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_ah.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrcAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia_ah. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L21354625109.2000004S2FS". (* [comment removed for export] *)
#[using="Type"] Lemma fsk_hint_eq : forall FS k, fsk_hint FS k = FS + 8 * k.
Proof. intros. unfold fsk_hint. destruct (Z.eqb_spec k 0); [subst; lia| reflexivity]. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L22355839458.4L53517058186.200000600:S2FS1kS2FS". (* [comment removed for export] *)
#[using="Type"] Lemma fsk_hint8_eq : forall FS k, fsk_hint8 FS k = FS + 8 * k + 8.
Proof. intros. unfold fsk_hint8. destruct (Z.eqb_spec k 0); [subst; lia| lia]. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L23357184889.4000008S2FS1k1i". (* [comment removed for export] *)
#[using="Type"] Lemma fsk_frame_eq : forall FS k i, fsk_frame FS k i = FS + 36864 + k * 2^20 + i * fsk_bytes k.
Proof. intros. unfold fsk_frame, fsk_bytes. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section FakeRep.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Hypothesis ASB : al_sb AL = 0x7fff8000.

  (* [comment removed for export] *)
  Definition smalloc_postk (k : Z) (SP FS BLK T CTX lo hint : Z) (fl : list byte)
      (ra gp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists (x5 x11 x12 x13 x14 x15 x16 x17 : word) (m' : mem) (r : Z),
      ms' = MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) x5 t1 t2 s0 s1 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo SP /\ smalloc_statics m' FS BLK T CTX /\ poison_statics m'
      /\ (exists (pos c : Z) (b : byte) (j1 j2 : list byte),
              let FB := fsk_frame FS k pos in
              r = FB /\ 0 <= c < 2^64 /\ pos = c mod fsk_n k /\ nth_error fl (Z.to_nat pos) = Some b /\ bv_unsigned b = 0
              /\ munch [(lo, SP); (fsk_hint FS k, fsk_hint8 FS k); (FS + fsk_foff k + pos, FS + fsk_foff k + pos + 1);
                        (FB, FB + fsk_bytes k); (shd FB, shd FB + 8 * 2^k)] m m'
              /\ rw_cells asegs m' (fsk_hint FS k) [C8 (Z_to_bv 64 (c + 1))]
              /\ u8arr asegs m' (FS + fsk_foff k) (upd fl (Z.to_nat pos) (Z_to_bv 8 1))
              /\ rw_cells asegs m' FB [CB 24 j1; C8 (Z_to_bv 64 SP); CB (Z.to_nat (fsk_bytes k - 40)) j2; C8 (Z_to_bv 64 (FS + fsk_foff k + pos))]
              /\ rw_cells asegs m' (shd FB) [CB (Z.to_nat (8 * 2^k)) (repeat (Z_to_bv 8 0) (Z.to_nat (8 * 2^k)))]).

  Definition smalloc_speck (k : Z) : Prop := forall
      (ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (SP FS BLK T CTX lo hint : Z) (fl : list byte) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      Timg BLK -> BLK + 4096 <= ACEIL -> 0x65f000 <= CTX -> CTX + 0x10000 <= ACEIL ->
      Timg T -> T + 4096 <= ACEIL ->
      (0x65f000 <= FS /\ Pband FS kFakeBytes) -> FS + kFakeBytes <= ACEIL -> FS mod 4096 = 0 -> 0 <= hint < 2^64 ->
      (Timg BLK /\ Tband BLK) -> (0x65f000 <= CTX /\ Pband CTX 0x10000) ->
      (CTX + 0x10000 <= FS \/ FS + kFakeBytes <= CTX) -> (BLK + 4096 <= FS \/ FS + kFakeBytes <= BLK) ->
      smalloc_statics m FS BLK T CTX -> poison_statics m ->
      crange CS BLK 4096 -> crange CS CTX 0x10000 -> crange CS T 4096 -> crange CS FS kFakeBytes ->
      (exists tb te : word, ro_cells asegs m (T + 48) [C8 tb; C8 te]) ->
      ro_cells asegs m (FS + 88) [C8 (Z_to_bv 64 20); C1 (Z_to_bv 8 0)] -> rw_cells asegs m (fsk_hint FS k) [C8 (Z_to_bv 64 hint)] ->
      u8arr asegs m (FS + fsk_foff k) fl -> Z.of_nat (length fl) = fsk_n k ->
      (forall i b, 0 <= i < fsk_n k -> nth_error fl (Z.to_nat i) = Some b -> bv_unsigned b = 0 ->
         exists junk sj, rw_cells asegs m (fsk_frame FS k i) [CB (Z.to_nat (fsk_bytes k)) junk]
                         /\ rw_cells asegs m (shd (fsk_frame FS k i)) [CB (Z.to_nat (8 * 2^k)) sj]) ->
      (exists i0 (b0 : byte), 0 <= i0 < fsk_n k /\ nth_error fl (Z.to_nat i0) = Some b0 /\ bv_unsigned b0 = 0) ->
      stk asegs m lo SP -> ACEIL <= lo -> lo <= SP - 208 -> SP <= 2^62 -> crange CS lo (SP - lo) -> mem_inv asegs m ->
      evtA asegs AL CS (smalloc_postk k SP FS BLK T CTX lo hint fl ra gp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
        (MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (A_SMALLOC k)) fc None m (seg_rom asegs)).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L37082788584.9000006S1k2Hk". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK ASB"] Lemma smalloc_speck_all : forall k, 0 <= k <= 5 -> smalloc_speck k.
  Proof.
    intros k Hk.
    assert (C : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5) by lia.
    destruct C as [-> | [-> | [-> | [-> | [-> | ->]]]]]; unfold smalloc_speck; intros.
    - exact (smalloc0_spec AL IMG ALWF CS CSOK ASB ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS BLK T CTX lo hint fl F fc m
               H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31).
    - exact (smalloc1_spec AL IMG ALWF CS CSOK ASB ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS BLK T CTX lo hint fl F fc m
               H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31).
    - exact (smalloc2_spec AL IMG ALWF CS CSOK ASB ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS BLK T CTX lo hint fl F fc m
               H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31).
    - exact (smalloc3_spec AL IMG ALWF CS CSOK ASB ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS BLK T CTX lo hint fl F fc m
               H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31).
    - exact (smalloc4_spec AL IMG ALWF CS CSOK ASB ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS BLK T CTX lo hint fl F fc m
               H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31).
    - exact (smalloc5_spec AL IMG ALWF CS CSOK ASB ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS BLK T CTX lo hint fl F fc m
               H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac kcases k :=
    let KC := fresh "KC" in
    first [ assert (KC : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10) by lia;
            destruct KC as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]]] ].

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L27764260380.8L37082788584.9000001007SS1k2Hk". (* [comment removed for export] *)
  #[using="Type"] Lemma fsk_sizes : forall k, 0 <= k <= 10 ->
    64 <= fsk_bytes k <= 65536 /\ 1 <= fsk_n k <= 16384 /\ fsk_n k * fsk_bytes k = 2^20 /\ 4096 <= fsk_foff k /\ fsk_foff k + fsk_n k <= 36864
    /\ fsk_bytes k mod 64 = 0 /\ 8 * 2^k = fsk_bytes k / 8 /\ fsk_bytes k = 64 * 2^k /\ 1 <= 2^k <= 1024.
  Proof. intros k Hk. unfold fsk_bytes, fsk_n, fsk_foff. kcases k; cbn; lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L37082788584.11L57274652772.1100000600?S1k2HkS2FS1i2Hi". (* [comment removed for export] *)
  #[using="Type"] Lemma fsk_frame_range : forall FS k i, 0 <= k <= 10 -> 0 <= i < fsk_n k ->
    FS + 36864 + k * 2^20 <= fsk_frame FS k i /\ fsk_frame FS k i + fsk_bytes k <= FS + 36864 + (k + 1) * 2^20.
  Proof. intros FS k i Hk Hi. rewrite fsk_frame_eq. revert Hi. unfold fsk_bytes, fsk_n. kcases k; cbn; intros; lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L24590162771.1300000=S2FS1k1i2Hk1H". (* [comment removed for export] *)
  #[using="Type"] Lemma fsk_frame_inside : forall FS k i, 0 <= k <= 10 -> 0 <= i < fsk_n k ->
    FS + 36864 <= fsk_frame FS k i /\ fsk_frame FS k i + fsk_bytes k <= FS + kFakeBytes.
  Proof. intros FS k i Hk Hi. pose proof (fsk_frame_range FS k i Hk Hi). unfold kFakeBytes. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L23225092089.16L37084885676.1400000I00OS1k1i2i'2Hk2Hi2NE3Hi'3Hk'S1k2Hk". (* [comment removed for export] *)
  #[using="Type"] Lemma fsk_frames_apart : forall FS k i k' i', 0 <= k <= 10 -> 0 <= i < fsk_n k -> 0 <= k' <= 10 -> 0 <= i' < fsk_n k' ->
    (k <> k' \/ i <> i') ->
    fsk_frame FS k i + fsk_bytes k <= fsk_frame FS k' i' \/ fsk_frame FS k' i' + fsk_bytes k' <= fsk_frame FS k i.
  Proof.
    intros FS k i k' i' Hk Hi Hk' Hi' NE.
    destruct (Z.eq_dec k k') as [<-|NK].
    - assert (i <> i') by lia. rewrite !fsk_frame_eq. revert Hi Hi' H. unfold fsk_bytes, fsk_n. kcases k; cbn; intros; nia.
    - pose proof (fsk_frame_range FS k i Hk Hi). pose proof (fsk_frame_range FS k' i' Hk' Hi'). nia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L59308579027.21L59308579027.22L62840394972.18L62840395738.1900000U01:01V022S2FS1k1i2k'2i'2Hk2Hi3Hk'3Hi'1E1A1H2H0S2FS1k1i2k'2i'2Hk2Hi3Hk'3Hi'1E1A1H2H0S1k1i2k'2i'2Hk2Hi3Hk'3Hi'2NKS1k1i2k'2i'2Hk2Hi3Hk'3Hi'2NI". (* [comment removed for export] *)
  #[using="Type"] Lemma fsk_frame_inj : forall FS k i k' i', 0 <= k <= 10 -> 0 <= i < fsk_n k -> 0 <= k' <= 10 -> 0 <= i' < fsk_n k' ->
    fsk_frame FS k i = fsk_frame FS k' i' -> k = k' /\ i = i'.
  Proof.
    intros FS k i k' i' Hk Hi Hk' Hi' E.
    destruct (Z.eq_dec k k') as [EK|NK]; [destruct (Z.eq_dec i i') as [EI|NI]; [auto|]|];
      (pose proof (fsk_frames_apart FS k i k' i' Hk Hi Hk' Hi' ltac:(lia)) as A; pose proof (fsk_sizes k Hk); pose proof (fsk_sizes k' Hk'); exfalso; lia).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L62709097385.1200000=S1k1i2Hk2Hi1H". (* [comment removed for export] *)
  #[using="Type"] Lemma fsk_flag_range : forall k i, 0 <= k <= 10 -> 0 <= i < fsk_n k -> 4096 <= fsk_foff k + i < 36864.
  Proof. intros k i Hk Hi. pose proof (fsk_sizes k Hk). lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L37082883970.12L50627804518.10L54788194858.1100000600A00IS1k2HkS2Hk2NE3Hk'S2k'3Hk'". (* [comment removed for export] *)
  #[using="Type"] Lemma fsk_flags_apart : forall k k', 0 <= k <= 10 -> 0 <= k' <= 10 -> k <> k' ->
    fsk_foff k + fsk_n k <= fsk_foff k' \/ fsk_foff k' + fsk_n k' <= fsk_foff k.
  Proof. intros k k' Hk Hk' NE. unfold fsk_foff, fsk_n. kcases k; kcases k'; cbn; lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L67435894232.10000009S2FS1k2Hk". (* [comment removed for export] *)
  #[using="Type"] Lemma fsk_hint_range : forall FS k, 0 <= k <= 10 -> FS <= fsk_hint FS k /\ fsk_hint FS k + 8 <= FS + 88 /\ fsk_hint8 FS k = fsk_hint FS k + 8.
  Proof. intros FS k Hk. rewrite fsk_hint_eq, fsk_hint8_eq. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L29784457886.9000001S". (* [comment removed for export] *)
  #[using="Type"] Lemma shd_eq : forall p, 0 <= p -> shd p = 0x7fff8000 + p / 8.
  Proof. intros p Hp. unfold shd. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L30572155012.12L4113529650.12 L61028789280.12L62368434708.1200000;00A00G00OS1p1d2Hp2HdS1p2HpS1p2HpS1p1d2Hp". (* [comment removed for export] *)
  #[using="Type"] Lemma shd_add8 : forall p d, 0 <= p -> p mod 8 = 0 -> 0 <= d -> shd (p + 8 * d) = shd p + d.
  Proof. intros p d Hp Hm Hd. rewrite !shd_eq by lia. rewrite Z.mul_comm, Z.div_add by lia. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  
  (* [comment removed for export] *)
  
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma lb_remove_notin : forall (LF : list blk) A, List.NoDup (map fst LF) -> forall n, ~ In (A, n) (lb_remove A LF).
  Proof.
    induction LF as [|[B j] LF IH]; intros A ND n; cbn; [tauto|].
    cbn in ND. inversion ND; subst. destruct (Z.eqb_spec B A) as [->|NE].
    - intros IN. apply H1. apply in_map_iff. exists (A, n). split; [reflexivity| exact IN].
    - cbn. intros [E|IN]; [congruence|]. exact (IH A H2 n IN).
  Qed.

  #[using="Type"] Lemma lb_remove_nodup : forall (LF : list blk) A, List.NoDup (map fst LF) -> List.NoDup (map fst (lb_remove A LF)).
  Proof.
    induction LF as [|[B j] LF IH]; intros A ND; cbn; [constructor|].
    cbn in ND. inversion ND; subst. destruct (Z.eqb_spec B A) as [->|NE]; [exact H2|].
    cbn. constructor; [| apply IH; exact H2]. intros IN. apply H1. apply in_map_iff in IN. ddestruct IN as ([B' j'] & E & IN). cbn in E. subst B'.
    apply in_map_iff. exists (B, j'). split; [reflexivity| eapply In_lb_remove; exact IN].
  Qed.

  Definition flags_clause (FS : Z) (LF : list blk) (m : mem) (k : Z) (fl : list byte) : Prop :=
    u8arr asegs m (FS + fsk_foff k) fl /\ Z.of_nat (length fl) = fsk_n k
    /\ forall i, 0 <= i < fsk_n k -> exists b, nth_error fl (Z.to_nat i) = Some b
         /\ (bv_unsigned b = 0 -> ~ In (fsk_frame FS k i, fsk_bytes k) LF)
         /\ (bv_unsigned b <> 0 -> In (fsk_frame FS k i, fsk_bytes k) LF
               /\ ro_cells asegs m (fsk_frame FS k i + fsk_bytes k - 8) [C8 (Z_to_bv 64 (FS + fsk_foff k + i))]).

  
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L32612967951.34L36349165336.2800000L00ZS1k1i2fl2Hk2Hi3Hk02i03Hi02NIS1k1i2fl1L3Hi0". (* [comment removed for export] *)
  #[using="Type"] Lemma flags_update : forall FS LF LF' m m' k i fl (v : byte),
    0 <= k <= 10 -> 0 <= i < fsk_n k ->
    (* [comment removed for export] *)
    (forall k' i', 0 <= k' <= 10 -> 0 <= i' < fsk_n k' -> (k' <> k \/ i' <> i) ->
        (In (fsk_frame FS k' i', fsk_bytes k') LF <-> In (fsk_frame FS k' i', fsk_bytes k') LF')
        /\ (ro_cells asegs m (fsk_frame FS k' i' + fsk_bytes k' - 8) [C8 (Z_to_bv 64 (FS + fsk_foff k' + i'))] ->
            ro_cells asegs m' (fsk_frame FS k' i' + fsk_bytes k' - 8) [C8 (Z_to_bv 64 (FS + fsk_foff k' + i'))])) ->
    (* [comment removed for export] *)
    ((bv_unsigned v = 0 -> ~ In (fsk_frame FS k i, fsk_bytes k) LF')
     /\ (bv_unsigned v <> 0 -> In (fsk_frame FS k i, fsk_bytes k) LF' /\ ro_cells asegs m' (fsk_frame FS k i + fsk_bytes k - 8) [C8 (Z_to_bv 64 (FS + fsk_foff k + i))])) ->
    (* [comment removed for export] *)
    (forall k' fl', 0 <= k' <= 10 -> k' <> k -> Z.of_nat (length fl') = fsk_n k' -> u8arr asegs m (FS + fsk_foff k') fl' -> u8arr asegs m' (FS + fsk_foff k') fl') ->
    u8arr asegs m' (FS + fsk_foff k) (upd fl (Z.to_nat i) v) ->
    flags_clause FS LF m k fl ->
    (forall k0, 0 <= k0 <= 10 -> exists fl0, flags_clause FS LF m k0 fl0) ->
    (forall k0, 0 <= k0 <= 10 -> exists fl0, flags_clause FS LF' m' k0 fl0).
  Proof.
    (intros FS LF LF' m m' k i fl v Hk Hi OTH SLOT ARR' NEWA dd_H; ddestruct dd_H as (U & L & SL); intros FL k0 Hk0).
    destruct (Z.eq_dec k0 k) as [->|NK].
    - exists (upd fl (Z.to_nat i) v). split; [exact NEWA|]. split; [rewrite upd_length; exact L|].
      intros i0 Hi0. destruct (Z.eq_dec i0 i) as [->|NI].
      + exists v. split; [apply nth_error_upd_same; lia|]. exact SLOT.
      + ddestruct (SL i0 Hi0) as (b & NTH & Z0 & NZ). exists b. split; [rewrite nth_error_upd_other by lia; exact NTH|].
        destruct (OTH k i0 Hk Hi0 ltac:(right; exact NI)) as [IFF RO].
        split; [intros Hb IN; apply (Z0 Hb); apply IFF; exact IN|].
        intros Hb. destruct (NZ Hb) as [IN R]. split; [apply IFF; exact IN| apply RO; exact R].
    - ddestruct (FL k0 Hk0) as (fl0 & U0 & L0 & SL0).
      exists fl0. split; [apply ARR'; [exact Hk0| exact NK| exact L0| exact U0]|]. split; [exact L0|].
      intros i0 Hi0. ddestruct (SL0 i0 Hi0) as (b & NTH & Z0 & NZ). exists b. split; [exact NTH|].
      destruct (OTH k0 i0 Hk0 Hi0 ltac:(left; exact NK)) as [IFF RO].
      split; [intros Hb IN; apply (Z0 Hb); apply IFF; exact IN|].
      intros Hb. destruct (NZ Hb) as [IN R]. split; [apply IFF; exact IN| apply RO; exact R].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00D0?L10085779884.41L10351937755.35L1048629717.36 L15007571935.35L17868274042.41L17874552130.44L17875059905.36L19524840938.36L2264624176.44 L23521016124.35L23521070485.36L27159752351.44L28091884888.35L40471561295.42L59308579027.45L60653662710.36L66674758325.41L66676862605.44L66677370638.36L6755570068.35 00000F00Q00f01401L02202G02W03703B03M04704G04k05W05e06:06Z06o075S2FS1k1i2Hk2fl2FR2k'1HS1k1i2Hi2flS2FS1k1i3FSL2Hk2fl2FRS2FS1k1i2fl2FRS2FS1k1i3FSL2Hk2Hi2fl2SZS2FS1k1i3FSL2Hk2Hi2fl2SZ2k'3Hk'2FR3fl'S2FS1k1i3FSL2Hk2fl2FRS1k1i2Hk2Hi2fl1LS2FS1k1i2Hk2fl2FR2k'2i'3Hk'1H2H0S2FS1k1i2flS2FS1k1i2flS2FS1k1i2Hk2Hi2fl2FR2SZ2k'3fl'3Hk'2L'1H2H0S1k1i2Hk2Hi2fl1LS1k1i2Hk2Hi2fl1L2FR2SZ2k'3fl'3Hk'2NKS1k1i2Hk2Hi2fl1L2FR2SZ2k'2i'3Hk'3Hi'2NE1H2H0S2FS1k1i2fl2FRS2FS1k1i3FSH2Hk2fl2FRS2FS1k1i3FSH2Hk2fl2FR2k'3Hk'3fl'S2FS1k1i3FSH2Hk2fl2FRS1k2fl". (* [comment removed for export] *)
  #[using="Type"] Lemma fake_free_mem : forall FS LF m FB n,
    fake_rep FS LF m -> In (FB, n) LF -> 0x65f000 <= FS -> FS + kFakeBytes <= 2^64 ->
    exists k i, 0 <= k <= 10 /\ 0 <= i < fsk_n k /\ FB = fsk_frame FS k i /\ n = fsk_bytes k
      /\ FS + 4096 <= FS + fsk_foff k + i < FS + 36864
      /\ ro_cells asegs m (FB + n - 8) [C8 (Z_to_bv 64 (FS + fsk_foff k + i))]
      /\ (exists old, rw_cells asegs m (FS + fsk_foff k + i) [C1 old])
      /\ fake_rep FS (lb_remove FB LF) (write_to_mem m (wa (FS + fsk_foff k + i)) [Z_to_bv 8 0]).
  Proof.
    intros FS LF m FB n HR IN FSL FSH. dpose HR as (HD & HI & FL & WF & ND).
    destruct (WF _ IN) as (k & i & Hk & Hi & E). injection E as EB EN. subst FB n.
    ddestruct (FL k Hk) as (fl & U & L & SL). ddestruct (SL i Hi) as (b & NTH & Z0 & NZ).
    assert (Hb : bv_unsigned b <> 0) by (intros Hb; exact (Z0 Hb IN)).
    destruct (NZ Hb) as [_ RO]. pose proof (fsk_flag_range k i Hk Hi) as FR. pose proof (fsk_sizes k Hk) as SZ.
    dexists k, i. split; [exact Hk|]. split; [exact Hi|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [exact RO|].
    assert (W1 : wr_at asegs m (FS + fsk_foff k + i) 1).
    { destruct U as [_ W]. replace (FS + fsk_foff k + i) with (FS + fsk_foff k + i) by lia. eapply (wr_at_sub m (FS + fsk_foff k) (Z.of_nat (length fl)) i 1); [exact W| lia| lia| lia]. }
    split; [apply wr_at_high_C1; [exact W1| lia]|].
    (* [comment removed for export] *)
    unfold kFakeBytes in FSH.
    split; [| split; [| split; [| split]]].
    - eapply ro_cells_frame; [exact HD| lia| cbn; lia| cbn; lia].
    - intros k' Hk'. destruct (HI k' Hk') as [h R]. exists h. pose proof (fsk_hint_range FS k' Hk').
      eapply rw_cells_frame; [exact R| lia| cbn; lia| cbn; lia].
    - change (forall k0, 0 <= k0 <= 10 -> exists fl0, flags_clause FS (lb_remove (fsk_frame FS k i) LF) (write_to_mem m (wa (FS + fsk_foff k + i)) [Z_to_bv 8 0]) k0 fl0).
      eapply (flags_update FS LF _ m _ k i fl (Z_to_bv 8 0) Hk Hi).
      + intros k' i' Hk' Hi' NE. split.
        * split; [| apply In_lb_remove]. intros IN'. apply In_lb_remove_keep; [exact IN'|].
          intros E. destruct (fsk_frame_inj FS k' i' k i Hk' Hi' Hk Hi E); lia.
        * intros R. pose proof (fsk_frame_range FS k' i' Hk' Hi'). pose proof (fsk_sizes k' Hk').
          eapply ro_cells_frame; [exact R| lia| cbn; lia| cbn; lia].
      + split; [intros _; apply lb_remove_notin; exact ND|]. intros NZ0. exfalso. apply NZ0. reflexivity.
      + intros k' fl' Hk' NK L' U'. pose proof (fsk_flags_apart k k' Hk Hk' ltac:(lia)). pose proof (fsk_sizes k' Hk').
        eapply u8arr_frame; [exact U'| lia| cbn; lia| cbn; lia].
      + replace (FS + fsk_foff k + i) with (FS + fsk_foff k + i) by lia. apply (u8arr_write asegs m (FS + fsk_foff k) fl i (Z_to_bv 8 0) U). lia.
      + split; [exact U|]. split; [exact L| exact SL].
      + exact FL.
    - intros fb INr. apply WF. eapply In_lb_remove. exact INr.
    - apply lb_remove_nodup. exact ND.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0?L13436643369.9 L32016765145.9 L37080606594.10L39182896069.9 L43635736521.9 L45767137177.9 L50765718777.9 L52477052089.9 L58488182329.9 L62384653289.9 L63409259529.9 L68395259241.9 00000300600<00?00B00E00F00I00L00O00R00US1ES1ES1k2HkS1ES1ES1ESS1ES1ES1ES1ES1E". (* [comment removed for export] *)
  #[using="Type"] Lemma fsk_bytes_5 : forall k, 0 <= k <= 10 -> fsk_bytes k = 2048 -> k = 5.
  Proof. intros k Hk E. unfold fsk_bytes in E. kcases k; cbn in E; lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition fsfree_post (ra : word) (SP : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (FS FB lo : Z) (LF : list blk) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (p : Z),
      ms' = MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ FS + 4096 <= p /\ p < FS + 36864
      /\ munch [(lo, SP); (p, p + 1); (shd FB, shd FB + 256)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo SP
      /\ fake_rep FS (lb_remove FB LF) m'
      /\ rw_cells asegs m' (shd FB) [CB 256 (repeat (Z_to_bv 8 0xf5) 256)]
      /\ poison_statics m'.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00^0@L14706798952.114L18225962366.83 L18430954150.81 L18846737983.15 L18926377950.80 L21368258799.83 L22367780584.118L22378865908.114L25125923317.83 L27148707607.83 L2867918535.114 L31120624987.118L37560692386.117L38544870678.83 L41230358663.117L42849123771.83 L43282320887.109L43869663466.115L45048431041.109L49401083049.79 L49401427858.106L49403148465.109L49403331979.117L49403341654.68 L49403414802.115L49403508010.78 L49405263420.116L5425493621.83  L55278276664.107L57079958331.83 L57967111319.83 L59298150276.107L59308579027.118L60899574310.81 L62044566896.81 L62271005279.83 L64018711474.83 L65795800422.83 L66404384638.83 L67302715947.118L67871354175.83 L7816695118.107 L8691851944.109 L897730003.117  L9632000782.107 L9633866532.81  00000C00D00R01D01O01b02G02b03603F03Y04304K04c05^05o06B07:07H07S07a07o08@08H08Z08e09309H09[09l0:@0:i0;i0<Q0<^0=90=:0=[0><0>Y0?20?E0?S0@20@Y0A=S3hAR2FS2FB2fl2k'1HFS3hAR2FS2FB2flS3hAR2SP2FS2FB2lo3FSL3FSH5LOIMG1i3SHR1A1n2H12H22H3S3hAR2FS2flS3hAR2FS2FB1i2Hi2flS3hAR2FS2FB1i2Hi2fl2SZ2k'2i'3Hk'1H2H0S3hAR2FS2FB1i2Hi2fl2SZ2k'1HS3hAR2FS2FB1i2fl3FRRS3hAR2FS2FB1i2flS3hAR2FS2FB2fl2k'1HS3hAR2FS2FB2fl2k'2i'3Hk'1HS3hAR2FS2FB2fl2k'3fl'2H0S3hAR2SP2FS2FB2lo3SPL2flS3hAR2FS2FB3FSL1i2Hi2Hk2fl3FRR2SZ2PR3SHR2k'3fl'3Hk'2L'1H2H0S3hAR2FS2FB2fl2SZS3hAR2FS2FB1i2fl2PRS3hAR2FS2FB3FSL1i2Hi2Hk2fl1L3FRR2SZ2PR3SHR2k'3fl'3Hk'2NKS3hAR2FS2FB2flS3hAR2FS2flS3hAR2FS2FB2flS3hAR2FS2FB2flS3hAR2FS2FB2fl2k'S3hAR2FSS3hAR2FS2FB2fl3fl'S3hAR2FS2flS3hAR2FS2FB2flS3hAR2SP2FS2FB3SPH2flS3hAR2FS2FB1i2fl2PRS3hAR2FS2FB2fl2SZS3hAR2FS2FB1i2fl3FRRS3hAR2FS1i3FSL3FSH2Hi2Hk2fl3FRR2SZ3FB82PRS3hAR2FS2FB3FSL1i2Hi2Hk2fl1L3FRR2SZ2PR3SHR2k'2i'3Hk'3Hi'2NE1H2H0S3hAR2FS2FB3FSL1i2EB2Hi2Hk2fl3FRR2SZ3FB8S3hAR2FS1i2flS3hAR2FS2FB3FSH1i2fl3FRR2SZFS3hAR2FS2FB3FSL1i2Hi2Hk2fl3FRR2SZS3hAR2FS2FB3FSL1i2Hi2Hk2fl3FRR2SZS3hAR2FS2FB2fl2k'2i'3Hk'1H2H0S3hAR2FS2FB1i2fl1L3FRR2SZS3hAR2FS2FB1i2fl2PRS3hAR2FS2FB2flS3hAR2FS2FB2fl2k'3fl'3Hk'2L'2H0S3hAR2FS2FB3FSL1i2EB2Hi2Hk2fl3FRR2SZ2PRS3hAR2FS2FB3FSL1i2EB2Hi2Hk2fl3FRR2SZ". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK ASB"] Lemma fake_sfree5 : forall
      (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (SP FS FB lo : Z) (LF : list blk) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      fake_rep FS LF m -> In (FB, 2048) LF ->
      (0x65f000 <= FS /\ Pband FS kFakeBytes) -> FS + kFakeBytes <= ACEIL -> FS mod 4096 = 0 ->
      wr_at asegs m (shd FB) 256 -> crange CS FS kFakeBytes ->
      ro_cells asegs m A_F5WORD [C8 (Z_to_bv 64 f5word)] -> poison_statics m ->
      stk asegs m lo SP -> ACEIL <= lo -> lo <= SP - 16 -> SP <= 2^62 -> crange CS lo (SP - lo) -> mem_inv asegs m ->
      evtA asegs AL CS (fsfree_post ra SP gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FS FB lo LF m)
        (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FB) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 A_SFREE5) fc None m (seg_rom asegs)).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS FB lo LF F fc m
      HR IN FSL FSH FSA WS FCS F5 PS ST LOIMG SPL SPH SCS MI.
    dpose HR as (HD & HI & FL & WF & ND). unfold kFakeBytes in FSH, FSL.
    destruct (WF _ IN) as (k & i & Hk & Hi & E). injection E as EB EN.
    pose proof (fsk_bytes_5 k Hk ltac:(symmetry; exact EN)) as ->. clear EN.
    ddestruct (FL 5 ltac:(lia)) as (fl & U & L & SL). ddestruct (SL i Hi) as (b & NTH & Z0 & NZ).
    assert (Hb : bv_unsigned b <> 0) by (intros Hb; apply (Z0 Hb); rewrite <- EB; exact IN).
    destruct (NZ Hb) as [_ RO].
    pose proof (fsk_frame_range FS 5 i ltac:(lia) Hi) as FRR. pose proof (fsk_sizes 5 ltac:(lia)) as SZ.
    assert (FB8 : FB mod 8 = 0).
    { rewrite EB, fsk_frame_eq. replace (fsk_bytes 5) with 2048 by reflexivity.
      pose proof (Z.div_mod FS 4096 ltac:(lia)) as D. rewrite FSA, Z.add_0_r in D. rewrite D.
      replace (4096 * (FS / 4096) + 36864 + 5 * 2 ^ 20 + i * 2048) with ((512 * (FS / 4096) + 4608 + 5 * 2^17 + i * 256) * 8) by lia. apply Z_mod_mult. }
    destruct (wr_at_high_CB m (shd FB) 256 WS ltac:(rewrite shd_eq by lia; lia) ltac:(lia)) as [sj SH].
    replace (fsk_frame FS 5 i + fsk_bytes 5 - 8) with (FB + 2040) in RO by (rewrite EB; change (fsk_bytes 5) with 2048; lia).
    eapply evtA_mono.
    { eapply (sfree5_arr_spec AL IMG ALWF CS CSOK ASB) with (p := FS + fsk_foff 5 + i) (FL := FS + fsk_foff 5) (i := i) (fl := fl) (lo := lo) (old := [CB (Z.to_nat 256) sj]);
        first [exact RO | exact U | exact SH | exact F5 | exact PS | exact ST | exact LOIMG | exact SCS | exact MI | exact FB8 | reflexivity
              | rewrite EB; lia | rewrite L; lia | rewrite L; eapply crange_sub; [exact FCS| lia| unfold kFakeBytes; lia]
              | eapply crange_sub; [exact FCS| rewrite EB; lia| rewrite EB; unfold kFakeBytes; change (fsk_bytes 5) with 2048 in FRR; lia] | lia ]. }
    cbv beta. (intros ms' dd_H; ddestruct dd_H as (x5 & x6 & x7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & NEWA & SHF & PS' & ST')).
    unfold fsfree_post. deexists 15. dexists m', (FS + fsk_foff 5 + i). split; [reflexivity|].
    pose proof (fsk_flag_range 5 i ltac:(lia) Hi) as PR.
    split; [lia|]. split; [lia|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
    split; [| split; [exact SHF| exact PS']].
    (* [comment removed for export] *)
    assert (SHR : (FS + 11571200 <= 0x7fff7000 /\ 0x80000000 <= shd FB /\ shd FB + 256 <= 0x8fff7000)
                  \/ (0x10007fff8000 <= FS /\ 0x2008fff7000 <= shd FB /\ shd FB + 256 <= 0x10007fff8000))
      by (rewrite shd_eq by lia; rewrite EB in *; change (fsk_bytes 5) with 2048 in FRR; lia).
    assert (DJ : forall A n, (A + n <= FS + fsk_foff 5 + i \/ FS + fsk_foff 5 + i + 1 <= A) -> FS <= A -> A + n <= FS + 11571200 ->
                 disjoint_from [(lo, SP); (FS + fsk_foff 5 + i, FS + fsk_foff 5 + i + 1); (shd FB, shd FB + 256)] A n).
    { intros A n H1 H2 H3. cbn. clear -H1 H2 H3 LOIMG SHR FSL FSH. lia. }
    split; [| split; [| split; [| split]]].
    - eapply ro_cells_transport; [exact HD| exact MU| apply DJ; cbn; lia].
    - intros k' Hk'. destruct (HI k' Hk') as [h R]. exists h. pose proof (fsk_hint_range FS k' Hk').
      eapply rw_cells_transport; [exact R| exact MU| exact WM| apply DJ; cbn; lia].
    - change (forall k0, 0 <= k0 <= 10 -> exists fl0, flags_clause FS (lb_remove FB LF) m' k0 fl0).
      eapply (flags_update FS LF _ m m' 5 i fl (Z_to_bv 8 0) ltac:(lia) Hi).
      + intros k' i' Hk' Hi' NE. split.
        * split; [| apply In_lb_remove]. intros IN'. apply In_lb_remove_keep; [exact IN'|].
          rewrite EB. intros E. destruct (fsk_frame_inj FS k' i' 5 i Hk' Hi' ltac:(lia) Hi E); lia.
        * intros R. pose proof (fsk_frame_range FS k' i' Hk' Hi'). pose proof (fsk_sizes k' Hk').
          pose proof (fsk_frames_apart FS k' i' 5 i Hk' Hi' ltac:(lia) Hi NE) as AP. rewrite <- EB in AP. change (fsk_bytes 5) with 2048 in AP.
          eapply ro_cells_transport; [exact R| exact MU| apply DJ; cbn; lia].
      + split; [intros _; rewrite <- EB; apply lb_remove_notin; exact ND|]. intros NZ0. exfalso. apply NZ0. reflexivity.
      + intros k' fl' Hk' NK L' U'. pose proof (fsk_flags_apart 5 k' ltac:(lia) Hk' ltac:(lia)). pose proof (fsk_sizes k' Hk').
        eapply u8arr_transport; [exact U'| exact MU| exact WM| apply DJ; lia].
      + exact NEWA.
      + split; [exact U|]. split; [exact L| exact SL].
      + exact FL.
    - intros fb INr. apply WF. eapply In_lb_remove. exact INr.
    - apply lb_remove_nodup. exact ND.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L21468897293.15000008S2FB3mid". (* [comment removed for export] *)
  #[using="Type"] Lemma ro_last_of_frame : forall m FB j1 j2 (w p : word) mid,
    rw_cells asegs m FB [CB 24 j1; C8 w; CB mid j2; C8 p] -> ro_cells asegs m (FB + (32 + Z.of_nat mid)) [C8 p].
  Proof.
    intros m FB j1 j2 w p mid H.
    apply (proj1 (rw_cells_app asegs m FB [CB 24 j1; C8 w; CB mid j2] [C8 p])) in H. destruct H as [_ H].
    replace (FB + Z.of_nat (cells_size [CB 24 j1; C8 w; CB mid j2])) with (FB + (32 + Z.of_nat mid)) in H by (cbn [cells_size csize]; lia).
    destruct H as [H _]. exact H.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L266172279.25  L35728109585.27L36340077366.23L36340470582.25L5449841244.25 L59308516196.2500000A00Q00g01=01M01_S2LF1k2fl1N2SZ2LES2LF1k2fl1N1i2HiS2LF1k2fl2Hk1N2SZ1i2HiS2LF1k2fl2Hk1N2SZ1i2HiS2LF1k2fl1N1i2HiS2LF1k2fl1N3LEN2LE". (* [comment removed for export] *)
  #[using="Type"] Lemma free_slot_of_flags : forall FS LF m k fl, 0 <= k <= 10 -> flags_clause FS LF m k fl -> Z.of_nat (length LF) < fsk_n k ->
    exists i0 (b0 : byte), 0 <= i0 < fsk_n k /\ nth_error fl (Z.to_nat i0) = Some b0 /\ bv_unsigned b0 = 0.
  Proof.
    (intros FS LF m k fl Hk dd_H; ddestruct dd_H as (U & L & SL); intros LEN). pose proof (fsk_sizes k Hk) as SZ.
    set (N := fsk_n k) in *.
    set (P := fun i : nat => match nth_error fl i with Some b => bv_unsigned b =? 0 | None => false end).
    destruct (existsb P (seq 0 (Z.to_nat N))) eqn:E.
    - apply existsb_exists in E. ddestruct E as (i & Hi & Pi). apply in_seq in Hi. unfold P in Pi.
      destruct (nth_error fl i) as [b|] eqn:NB; [| discriminate]. apply Z.eqb_eq in Pi.
      dexists (Z.of_nat i), b. rewrite Nat2Z.id. split; [lia|]. split; [exact NB| exact Pi].
    - exfalso.
      assert (ALLIN : forall i, (i < Z.to_nat N)%nat -> In (fsk_frame FS k (Z.of_nat i), fsk_bytes k) LF).
      { intros i Hi. ddestruct (SL (Z.of_nat i) ltac:(lia)) as (b & NB & _ & NZ). rewrite Nat2Z.id in NB. apply NZ. intros Zb.
        assert (X : existsb P (seq 0 (Z.to_nat N)) = true).
        { apply existsb_exists. exists i. split; [apply in_seq; lia|]. unfold P. rewrite NB. apply Z.eqb_eq. exact Zb. }
        rewrite E in X. discriminate. }
      set (Lm := map (fun i => (fsk_frame FS k (Z.of_nat i), fsk_bytes k)) (seq 0 (Z.to_nat N))).
      assert (ND : List.NoDup Lm).
      { subst Lm. apply List.NoDup_map_NoDup_ForallPairs; [| apply List.seq_NoDup]. intros i j _ _ Hij. injection Hij as E1.
        rewrite !fsk_frame_eq in E1. apply Nat2Z.inj. nia. }
      assert (INC : incl Lm LF).
      { intros x Hx. subst Lm. apply in_map_iff in Hx. ddestruct Hx as (i & <- & Hi). apply in_seq in Hi. apply ALLIN. lia. }
      pose proof (List.NoDup_incl_length ND INC) as LE. subst Lm. rewrite length_map, length_seq in LE. apply Nat2Z.inj_le in LE. rewrite Z2Nat.id in LE by lia. unfold blk in *. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition fsmalloc_post (k SP FS BLK T CTX lo : Z) (LF : list blk)
      (ra gp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists (x5 x11 x12 x13 x14 x15 x16 x17 : word) (m' : mem) (r : Z),
      ms' = MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) x5 t1 t2 s0 s1 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo SP /\ smalloc_statics m' FS BLK T CTX /\ poison_statics m'
      /\ (exists junk,
              FS + 36864 <= r /\ r + fsk_bytes k <= FS + kFakeBytes /\ r mod 64 = 0
              /\ (forall B j, In (B, j) LF -> r + fsk_bytes k <= B \/ B + j <= r)
              /\ munch [(lo, SP); (FS, FS + 36864); (r, r + fsk_bytes k); (shd r, shd r + fsk_bytes k / 8)] m m'
              /\ fake_rep FS ((r, fsk_bytes k) :: LF) m'
              /\ rw_cells asegs m' r [CB (Z.to_nat (fsk_bytes k)) junk]
              /\ rw_cells asegs m' (shd r) [CB (Z.to_nat (fsk_bytes k / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (fsk_bytes k / 8)))]).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00j0@L11806181725.96 L12134895350.97 L14896750811.139L14897095672.136L18600298032.108L18926753734.95 L19346798304.109L19615217426.6  L19997679745.8  L21513998387.109L22348223232.6  L23502572520.16 L23785511580.139L24570982710.85 L2701790260.6   L31120624987.16 L31787446020.137L3454296978.137 L3454298502.109 L35005452208.16 L40471562708.145L41035192193.8  L41122901283.17 L41126948666.21 L41415910982.97 L43712215332.105L49158489005.104L49160846223.126L49160912126.105L52067225200.107L52069633490.136L52071383766.137L52989384624.104L56093469787.139L58779418932.8  L59296251267.5  L59308579027.147L59314955108.140L61024696820.107L61028844156.136L61031299651.108L63113918959.109L63380682926.107L6510840928.22  L6510841057.21  L65427371602.98 L66353385618.2  L66879307307.142L67302715947.16 L67318314345.107L67863747923.104L6798206220.10  L6800501266.8   L68148629793.109L7529257913.104 L8208529817.4   L8806423876.10  L981539133.98   00000D00[01J02902Z02n03j03k04C04_05205c06R06f07907V08N09N09g0:G0;[0;g0<e0=o0>C0?J0?c0@C0@\0A60Ac0BP0C10C]0Ci0D?0ET0F?0FU0G>0GT0Gm0HC0IN0JV0Jo0K50LD0Ld0MH0M^0N>0NT0OP0Ol0Om0PL0PbS3hAR1k2FS2LF3LFB2flS3hAR1k2FS2LF2Hk3LFB2flS3hAR1k2FS2LF2Hk3LFB2fl2SZ3pos1c2j12j22FB2L12L2S3hAR1k2FS2LF2Hk3LFB2fl2SZ3pos1c2j12j22FB2L12L2S3hAR1k2FS2LF2Hk3LFB2fl2SZ1i2D81HS3hAR1k2FS2LF3LFB2flS3hAR1k2FS3BLK2LF2Hk3LFB2BL3FSL3BHI4FSL'4Hk102fl2SZ3DFS1i2FRFS1k2FS2SZ3pos2PB2k'1H2H0S3hAR1k2FS2LF2Hk3LFB2fl2SZ1iS1k2FS2Hk3pos2FB2FRS3hAR1k2FS2Hk4FSL'3pos2FB2FR2PR2k'2i'3Hk'1H2H02APS3hAR1k2FS2LF2Hk3LFB2fl2SZ3pos1c2j12j22FB2L12L2S3hAR1k2FS2LF2Hk3LFBS1k2FS2Hk3pos2FB2FRS3hAR1k2FS3pos2FB2k'2i'3Hk'1HS3hAR1k2FS2LF2Hk3LFB2fl2SZ3pos1c2j12j22HP2FB2L12L22D82DVS3hAR1k2FS2LF2Hk3LFB4Hk102fl2SZ3pos1c2j12j22HP2FB2PB2L12L22D82DVS3hAR1k2FS2LF3LFB2fl1i2DBS3hAR1k2FS3pos2FB2k'2i'3Hk'1H2H0S3hAR1k2FS3BLK2LF2Hk3LFB2BL3FSL3BHI4FSL'2fl2SZ3pos1c2j12j22Hc2FB2L12L23SLO2k'3fl'2NKS1k2FS2k'2H0S3hAR1k2SP2FS2lo2Hk5LOIMG4FSL'4FSH'3HHR3pos2FB2FR2PR2B12B23SLOS3hAR1k2SP2FS2lo2Hk5LOIMG4FSL'4FSH'3HHR3pos2FB2FR2PR2B12B23SLO2k'3Hk'2NK1HS3hAR1k2FS2LF3LFB2flS3hAR1k2FS3BLK3CTX2LF2Hk3LFB2BL3FSL3BHI3CHI4FSL'4Hk102fl2SZ3DFS1i2Hi2FRS3hAR1k2FS2LF3LFB2fl2SZ1iS3hAR1k2FS2LF3LFB2fl2SZ3pos1c2FBS3hAR1k2FS2LF3LFB2fl2SZ1iS3hAR1k2FS2LF3LFB3FSL2fl1iS3hAR1k2FS2LF3LFB3FSL2fl3pos1c2j12j22FB2L12L2S3hAR1k2FS2LF3LFB3FSL2fl3pos1c2j12j22FB2L12L2S3hAR1k2FS2LF2Hk3LFB4Hk102fl1i2FRS3hAR1k2FS2LF2Hk3LFB2fl2SZ3pos1c2j12j22L12L2S1k2FS2k'2H0S3hAR2FS4FSL'4FSH'3DFSS3hAR1k2FS3BLK2LF2Hk3LFB2BL3FSL3BHI4FSL'2fl2SZ3pos1c2j12j22Hc2L12L23SLO2k'2i'2NE1H2H0S3hAR1k2FS2LF3LFB2fl3pos1c2j12j22FB2L12L21ES3hAR1k2FS2LF3LFB2fl1iS3hAR1k2FS2LF3LFB2fl3pos1c2j12j22FB2L12L2S3hAR1k2FS2LF3LFB2fl1iS3hAR1k2FS2LF3LFB2fl1i2DBS3hAR1k2FS2LF3LFB2fl1iS3hAR1k2SP2FS2lo2Hk5LOIMG4FSL'4FSH'3HHR3pos2FB2FR2PR2B12B23SLO1A1n2H12H22H3S3hAR1k2SP2FS2lo5LOIMG4FSL'4FSH'3HHR3pos2FB2PR2B12B23SLO1A1n2H12H22H32H4S3hAR1k2FS2LF2Hk3LFB2fl1HS1h2HBS3hAR1k2FS3BLK2LF2Hk3LFB2BL3FSL3BHI4FSL'2fl2SZ3pos1c2j12j22Hc2L12L23SLO2k'2i'1HS3hAR1k2FS3pos2FB2k'2i'3Hk'1H2H0S3hAR1k2FS2LF2Hk3LFB4Hk102fl2SZ1i2HiS3hAR1k2FS2LF3LFB2fl1iS1k2FS2Hk2SZ3pos2FB2FR3HFB2D82DVS1k2FS2Hk2SZ1i2FR2D81HS3hAR1k2FS3BLK2LF2Hk3LFB2BL3FSL3BHI4FSL'4Hk102fl2SZ3DFS1i2FRS3hAR1k2FS2LF2Hk3LFB2fl1i2FRFS1k2SP2FS2lo3HHR3pos2FB2PR1y2HyS3hAR1k2FS2LF3LFB2fl1H". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK ASB"] Lemma fake_smalloc : forall (k : Z)
      (ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (SP FS BLK T CTX lo : Z) (LF : list blk) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      0 <= k <= 5 -> fake_rep FS LF m -> (length LF < 512)%nat ->
      wr_at asegs m (FS + 36864) (11 * 2^20) -> wr_at asegs m (shd (FS + 36864)) (11 * 2^17) ->
      Timg BLK -> BLK + 4096 <= ACEIL -> 0x65f000 <= CTX -> CTX + 0x10000 <= ACEIL ->
      Timg T -> T + 4096 <= ACEIL ->
      (0x65f000 <= FS /\ Pband FS kFakeBytes) -> FS + kFakeBytes <= ACEIL -> FS mod 4096 = 0 ->
      (Timg BLK /\ Tband BLK) -> (0x65f000 <= CTX /\ Pband CTX 0x10000) ->
      (CTX + 0x10000 <= FS \/ FS + kFakeBytes <= CTX) -> (BLK + 4096 <= FS \/ FS + kFakeBytes <= BLK) ->
      smalloc_statics m FS BLK T CTX -> poison_statics m ->
      crange CS BLK 4096 -> crange CS CTX 0x10000 -> crange CS T 4096 -> crange CS FS kFakeBytes ->
      (exists tb te : word, ro_cells asegs m (T + 48) [C8 tb; C8 te]) ->
      stk asegs m lo SP -> ACEIL <= lo -> lo <= SP - 208 -> SP <= 2^62 -> crange CS lo (SP - lo) -> mem_inv asegs m ->
      evtA asegs AL CS (fsmalloc_post k SP FS BLK T CTX lo LF ra gp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
        (MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (A_SMALLOC k)) fc None m (seg_rom asegs)).
  Proof.
    intros k ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS BLK T CTX lo LF F fc m
      Hk HR LFB WF1 WF2 BL BH CL CH TL TH FSL FSH FSA BHI CHI SEP1 SEP2 SS PS BCS CCS TCS FCS TT ST LOIMG SPL SPH SCS MI.
    dpose HR as (HD & HI & FL & WF & ND).
    pose proof FSL as FSL'. pose proof FSH as FSH'. unfold kHighMemBeg, kFakeBytes in FSL', FSH'.
    assert (Hk10 : 0 <= k <= 10) by lia.
    ddestruct (FL k Hk10) as (fl & U & L & SL). destruct (HI k Hk10) as [h HC].
    pose proof (fsk_sizes k Hk10) as SZ. pose proof (fsk_hint_range FS k Hk10) as HHR.
    pose proof (bv_unsigned_in_range 64 h) as HB. change (bv_modulus 64) with (2^64) in HB.
    rewrite <- (Z_to_bv_bv_unsigned h) in HC.
    pose proof (Z.div_mod FS 4096 ltac:(lia)) as DFS. rewrite FSA, Z.add_0_r in DFS.
    assert (M8 : (FS + 36864) mod 8 = 0) by (rewrite DFS; replace (4096 * (FS / 4096) + 36864) with ((512 * (FS / 4096) + 4608) * 8) by lia; apply Z_mod_mult).
    eapply evtA_mono.
    { eapply (smalloc_speck_all k Hk) with (hint := bv_unsigned h) (fl := fl) (lo := lo) (BLK := BLK) (T := T) (CTX := CTX) (FS := FS) (SP := SP);
        first [exact BL | exact BH | exact CL | exact CH | exact TL | exact TH | exact FSL | exact FSH | exact FSA | exact BHI | exact CHI | exact SEP1 | exact SEP2
              | exact SS | exact PS | exact BCS | exact CCS | exact TCS | exact FCS | exact TT | exact HD | exact HC | exact U | exact L
              | exact ST | exact LOIMG | exact SPL | exact SPH | exact SCS | exact MI | clear -HB; lia | idtac| idtac].
      2:{ (* [comment removed for export] *)
          apply (free_slot_of_flags FS LF m k fl Hk10); [split; [exact U| split; [exact L| exact SL]]|].
          assert (512 <= fsk_n k) by (unfold fsk_n; assert (2^9 <= 2^(14 - k)) by (apply Z.pow_le_mono_r; lia); lia). lia. }
      (* [comment removed for export] *)
      intros i b Hi NTH Hb. pose proof (fsk_frame_range FS k i Hk10 Hi) as FR.
      assert (D8 : (k * 2^20 + i * fsk_bytes k) mod 8 = 0).
      { replace (k * 2^20 + i * fsk_bytes k) with ((k * 2^17 + i * (8 * 2^k)) * 8) by (unfold fsk_bytes; ring). apply Z_mod_mult. }
      assert (WFi : wr_at asegs m (fsk_frame FS k i) (fsk_bytes k)).
      { replace (fsk_frame FS k i) with (FS + 36864 + (fsk_frame FS k i - (FS + 36864))) by lia. eapply wr_at_sub; [exact WF1| lia| lia| lia]. }
      destruct (wr_at_high_CB m (fsk_frame FS k i) (fsk_bytes k) WFi ltac:(lia) ltac:(lia)) as [junk FRM0].
      exists junk.
      assert (SHE : shd (fsk_frame FS k i) = shd (FS + 36864) + (k * 2^20 + i * fsk_bytes k) / 8).
      { rewrite fsk_frame_eq. replace (FS + 36864 + k * 2 ^ 20 + i * fsk_bytes k) with (FS + 36864 + 8 * ((k * 2^20 + i * fsk_bytes k) / 8)).
        2:{ pose proof (Z.div_mod (k * 2^20 + i * fsk_bytes k) 8 ltac:(lia)). lia. }
        rewrite shd_add8; [reflexivity| lia| exact M8| apply Z.div_pos; lia]. }
      assert (DB : 0 <= (k * 2^20 + i * fsk_bytes k) / 8 /\ (k * 2^20 + i * fsk_bytes k) / 8 + 8 * 2^k <= 11 * 2^17).
      { pose proof (Z.div_mod (k * 2^20 + i * fsk_bytes k) 8 ltac:(lia)). rewrite fsk_frame_eq in FR. clear -H D8 FR SZ Hk. lia. }
      destruct (wr_at_high_CB m (shd (fsk_frame FS k i)) (8 * 2^k)
                  ltac:(rewrite SHE; eapply (wr_at_sub m (shd (FS + 36864)) (11 * 2^17)); [exact WF2| lia| lia| lia])
                  ltac:(rewrite shd_eq by lia; lia) ltac:(lia)) as [sj SH0].
      exists sj. split; [exact FRM0| exact SH0]. }
    cbv beta. (intros ms' dd_H; ddestruct dd_H as (x5 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & m' & r & -> & WM & MI' & ST' & SS' & PS' & CASES)).
    unfold fsmalloc_post. dexists x5, x11, x12, x13, x14, x15, x16, x17, m', r. split; [reflexivity|].
    split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact SS'|]. split; [exact PS'|].
    ddestruct CASES as (pos & c & b & j1 & j2 & Hr & Hc & HP & NTH & Hb & MU & HC' & U' & FRM & SHZ).
    { (* [comment removed for export] *)
      cbv zeta in *. subst r.
      set (FB := fsk_frame FS k pos) in *.
      assert (PB : 0 <= pos < fsk_n k) by (rewrite HP; apply Z.mod_pos_bound; lia).
      pose proof (fsk_frame_range FS k pos Hk10 PB) as FR. change (fsk_frame FS k pos) with FB in FR. pose proof (fsk_flag_range k pos Hk10 PB) as PR.
      assert (HFB : FB = FS + 36864 + k * 2^20 + pos * fsk_bytes k) by (subst FB; apply fsk_frame_eq).
      ddestruct (SL pos PB) as (b0 & NTH0 & Z0 & _). rewrite NTH in NTH0. injection NTH0 as <-.
      pose proof (Z0 Hb) as NIN.
      assert (NEQ : forall k' i', 0 <= k' <= 10 -> 0 <= i' < fsk_n k' -> In (fsk_frame FS k' i', fsk_bytes k') LF -> k' <> k \/ i' <> pos).
      { intros k' i' Hk' Hi' IN. destruct (Z.eq_dec k' k) as [->|]; [| left; assumption]. destruct (Z.eq_dec i' pos) as [->|]; [| right; assumption].
        exfalso. exact (NIN IN). }
      pose proof FRM as [[WFJ _] _]. cbn in WFJ. ddestruct WFJ as (L1 & _ & L2 & _).
      exists (j1 ++ le8 (Z_to_bv 64 SP) ++ j2 ++ le8 (Z_to_bv 64 (FS + fsk_foff k + pos))).
      assert (SHR : shd FB = shd (FS + 36864) + (k * 2^20 + pos * fsk_bytes k) / 8 /\ 0 <= (k * 2^20 + pos * fsk_bytes k) / 8 /\ (k * 2^20 + pos * fsk_bytes k) / 8 + 8 * 2^k <= 11 * 2^17).
      { assert (D8 : (k * 2^20 + pos * fsk_bytes k) mod 8 = 0).
        { replace (k * 2^20 + pos * fsk_bytes k) with ((k * 2^17 + pos * (fsk_bytes k / 8)) * 8) by (clear -SZ; nia). apply Z_mod_mult. }
        pose proof (Z.div_mod (k * 2^20 + pos * fsk_bytes k) 8 ltac:(lia)) as DV.
        split; [| clear -DV D8 FR SZ Hk HFB; lia].
        rewrite HFB. replace (FS + 36864 + k * 2 ^ 20 + pos * fsk_bytes k) with (FS + 36864 + 8 * ((k * 2^20 + pos * fsk_bytes k) / 8)) by lia.
        rewrite shd_add8; [reflexivity| lia| exact M8| lia]. }
      (* [comment removed for export] *)
      assert (SLO : (FS + 11571200 <= 0x7fff7000 /\ 0x80000000 + 4608 <= shd (FS + 36864) /\ shd (FS + 36864) + 11 * 2^17 <= 0x8fff7000)
                    \/ (0x10007fff8000 <= FS /\ 0x2008fff7000 + 4608 <= shd (FS + 36864) /\ shd (FS + 36864) + 11 * 2^17 <= 0x10007fff8000))
        by (rewrite shd_eq by lia; clear -FSL' FSH' DFS; lia).
      split; [clear -FR Hk; lia|]. split; [unfold kFakeBytes; clear -FR Hk; lia|].
      split. { rewrite HFB, DFS. replace (4096 * (FS / 4096) + 36864 + k * 2 ^ 20 + pos * fsk_bytes k) with ((64 * (FS / 4096) + 576 + k * 2^14 + pos * 2^k) * 64).
               apply Z_mod_mult. unfold fsk_bytes. ring. }
      split. { intros B j IN. destruct (WF _ IN) as (k' & i' & Hk' & Hi' & E). injection E as -> ->.
               subst FB. apply (fsk_frames_apart FS k pos k' i' Hk10 PB Hk' Hi'). pose proof (NEQ k' i' Hk' Hi' IN). lia. }
      split. { eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]. ddestruct SHR as (_ & _ & _).
               replace (fsk_bytes k / 8) with (8 * 2^k) by lia. clear -HHR PR. intros y Hy. lia. }
      assert (DJ : forall A n, (A + n <= FS \/ FS + 36864 <= A) -> (A + n <= FB \/ FB + fsk_bytes k <= A) -> FS <= A -> A + n <= FS + 11571200 ->
                   disjoint_from [(lo, SP); (fsk_hint FS k, fsk_hint8 FS k); (FS + fsk_foff k + pos, FS + fsk_foff k + pos + 1); (FB, FB + fsk_bytes k); (shd FB, shd FB + 8 * 2 ^ k)] A n).
      { intros A n H1 H2 H3 H4. cbn. ddestruct SHR as (E & B1 & B2). rewrite E. clear -H1 H2 H3 H4 HHR PR LOIMG SLO B1 B2 FSL' FSH'. lia. }
      assert (DJ2 : forall A n, FS + 4096 <= A -> A + n <= FS + 36864 -> (A + n <= FS + fsk_foff k + pos \/ FS + fsk_foff k + pos + 1 <= A) ->
                   disjoint_from [(lo, SP); (fsk_hint FS k, fsk_hint8 FS k); (FS + fsk_foff k + pos, FS + fsk_foff k + pos + 1); (FB, FB + fsk_bytes k); (shd FB, shd FB + 8 * 2 ^ k)] A n).
      { intros A n H1 H2 H3. cbn. ddestruct SHR as (E & B1 & B2). rewrite E. clear -H1 H2 H3 HHR PR FR LOIMG SLO B1 B2 FSL' FSH' Hk. lia. }
      split.
      { split; [| split; [| split; [| split]]].
        - eapply ro_cells_transport; [exact HD| exact MU| cbn; ddestruct SHR as (E & B1 & B2); rewrite E; clear -HHR PR FR LOIMG SLO B1 B2 Hk FSL' FSH'; lia].
        - intros k' Hk'. destruct (Z.eq_dec k' k) as [->|NK]; [eexists; exact HC'|].
          destruct (HI k' Hk') as [h' R]. exists h'. pose proof (fsk_hint_range FS k' Hk'). rewrite fsk_hint_eq in *.
          eapply rw_cells_transport; [exact R| exact MU| exact WM| cbn; ddestruct SHR as (E & B1 & B2); rewrite E; clear -H HHR NK PR FR LOIMG SLO B1 B2 Hk Hk' FSL' FSH'; lia].
        - change (forall k0, 0 <= k0 <= 10 -> exists fl0, flags_clause FS ((FB, fsk_bytes k) :: LF) m' k0 fl0).
          eapply (flags_update FS LF _ m m' k pos fl (Z_to_bv 8 1) Hk10 PB).
          + intros k' i' Hk' Hi' NE. split.
            * split; [intros IN; right; exact IN|]. intros [E|IN]; [| exact IN]. injection E as E1 E2.
              exfalso. subst FB. destruct (fsk_frame_inj FS k' i' k pos Hk' Hi' Hk10 PB (eq_sym E1)); lia.
            * intros R. pose proof (fsk_frame_range FS k' i' Hk' Hi'). pose proof (fsk_sizes k' Hk').
              pose proof (fsk_frames_apart FS k' i' k pos Hk' Hi' Hk10 PB NE) as AP. fold FB in AP.
              eapply ro_cells_transport; [exact R| exact MU| apply DJ; cbn; clear -H H0 AP FR PR FSL' FSH' Hk Hk'; lia].
          + split; [intros E; exfalso; rewrite Z_to_bv_unsigned in E; vm_compute in E; lia|].
            intros _. split; [left; reflexivity|].
            pose proof (ro_last_of_frame m' FB j1 j2 _ _ _ FRM) as RL.
            replace (FB + (32 + Z.of_nat (Z.to_nat (fsk_bytes k - 40)))) with (fsk_frame FS k pos + fsk_bytes k - 8) in RL by (subst FB; lia). exact RL.
          + intros k' fl' Hk' NK L' U2. pose proof (fsk_flags_apart k k' Hk10 Hk' ltac:(lia)). pose proof (fsk_sizes k' Hk').
            eapply u8arr_transport; [exact U2| exact MU| exact WM| rewrite L'; apply DJ2; clear -H H0 PB SZ; lia].
          + exact U'.
          + split; [exact U|]. split; [exact L| exact SL].
          + exact FL.
        - intros fb [<-|IN]; [dexists k, pos; auto| apply WF; exact IN].
        - cbn. constructor; [| exact ND]. intros INM. apply in_map_iff in INM. ddestruct INM as ([B j] & E & IN). cbn in E. subst B.
          destruct (WF _ IN) as (k' & i' & Hk' & Hi' & E). injection E as E1 E2.
          destruct (fsk_frame_inj FS k' i' k pos Hk' Hi' Hk10 PB ltac:(subst FB; symmetry; exact E1)) as [-> ->]. subst j. exact (NIN IN). }
      split.
      { eapply rw_cells_reshape; [exact FRM| | cbn [cells_bytes cbytes]; rewrite !app_nil_r; reflexivity].
        cbn [cells_wf cell_wf]. split; [| exact I]. rewrite !app_length, L1, L2, !length_le8. lia. }
      replace (fsk_bytes k / 8) with (8 * 2^k) by lia. exact SHZ. }
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End FakeRep.

End ARUN_1.
