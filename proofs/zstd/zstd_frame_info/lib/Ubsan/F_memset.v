(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Arr.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import StrFun.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import STRW_memset.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg.
Import ListNotations.
Open Scope bv_scope.

Definition memset_entry := 0x1b640%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac with_arr tac :=
  lazymatch goal with
  | ARR : u8arr ?segs ?m ?A ?bs, FIL : filled ?cb ?bs _, LEN : length ?bs = _ |- _ => tac segs ARR FIL LEN A cb
  end.

(* [comment removed for export] *)
Ltac brute256 c Rc :=
  first [ apply word_eq_of_eqb | apply Z.eqb_eq | idtac ];
  repeat match goal with H : context [c] |- _ => tryif constr_eq H Rc then fail else clear H end;
  revert c Rc; apply brute256_ok; vm_compute; reflexivity.

(* [comment removed for export] *)
Ltac reg_val r :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
  end.
(* [comment removed for export] *)
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.

Lemma land4_of_aligned : forall x, (0 <= x)%Z -> (x mod 4 = 0)%Z -> Z.land x 4 = (x mod 8)%Z.
Proof.
  intros x Hx H4.
  transitivity (Z.land (x mod 8) 4).
  { change 8%Z with (2^3)%Z. Local Ltac2 Set LiaHints.tbl := fun () => "0020=26253754107.329784465626.3000004005S2H4S".
rewrite <- Z.land_ones by lia. change (Z.ones 3) with 7%Z.
    rewrite <- Z.land_assoc. reflexivity. }
  assert (R : (x mod 8 = 0 \/ x mod 8 = 4)%Z) by (OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  destruct R as [R|R]; rewrite R; reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition memset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' (bv_unsigned a0)
         [CB (Z.to_nat (bv_unsigned a2)) (repeat (Z_to_bv 8 (bv_unsigned a1 mod 256)) (Z.to_nat (bv_unsigned a2)))].

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Hypothesis MI0 : mem_inv usegs m.
  Hypothesis AB : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 <= 2^64 /\ 0 <= bv_unsigned a2 < 2^64)%Z.

  Notation A := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
  Notation POST := (memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m).
  (* [comment removed for export] *)
  Notation ST pc mm x11 x12 x13 x14 x15 x16 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Ltac fin_with cover :=
    zstep;
    with_arr ltac:(fun segs ARR FIL LEN A cb =>
      let E := fresh "E" in
      pose proof (filled_all _ _ _ FIL ltac:(cover)) as E;
      rewrite LEN in E; rewrite E in ARR;
      apply rw_cells_of_u8arr in ARR; rewrite repeat_length in ARR);
    finish; subst; assumption.
  Ltac fin := fin_with ltac:(intros j Hj; cbv beta; lia).
  Ltac disj_lia := first [ lia | right; lia | left; disj_lia ].

  (* [comment removed for export] *)
  Lemma memset_loop : forall (K : nat) (c p r e : Z) (m1 : word -> option byte) (bs : list byte) (Q : Z -> Prop)
      (x15 x16 : word),
    Z.to_nat r = K ->
    c = (bv_unsigned a1 mod 256)%Z ->
    u8arr usegs m1 A bs -> filled (Z_to_bv 8 c) bs Q -> length bs = Z.to_nat n ->
    mem_inv usegs m1 -> munch W m m1 -> wmono usegs m m1 ->
    (forall j, (0 <= j < p \/ e <= j < n) -> Q j)%Z ->
    (0 <= p)%Z -> (32 <= r)%Z -> (exists q, r = 4 * q)%Z -> (p + r <= n)%Z -> (e + 28 <= p + r)%Z ->
    evt usegs POST (ST 0x1b718 m1 (Z_to_bv 64 (A + p)) (Z_to_bv 64 (c * BC8)) (Z_to_bv 64 31) (Z_to_bv 64 r) x15 x16).
  Proof using AB.
    Local Ltac2 Set LiaHints.tbl := fun () => "00N0>11065392636.6411283365893.6818433022073.6019932234086.6420943972177.6422433216478.7623620033955.6925332637742.6426130493174.6930536993111.6332567987354.6732570090182.6832572771458.6732574867780.6834198808638.633746152322.65 3999782563.69 40139300643.6945380309975.6347638617054.7652488055643.6853305394057.6457932427401.6459667368592.6461508843596.6465822950878.7668607035491.648208580118.64 867403351.63  8690906023.64 00000I00V00^00_00g00o01901D01R01k02802V02e03503J03U03d03n04C04K04\04h05=05H05S05[06006106F06NS2HK2Hp2Hr3Hq43Hpr3LEN2KKS2HK3LEN1l2l0S2HK3LENFS2HK3LENS2HK3LENS2HK3LEN1HS2HK3LEN2KKS2HK3LEN3Hge1HS2AB2HK2Hp2Hr3Hq43Hpr3LENS2HK3LEN2Hj1lS2HK2Hp2Hr3Hq42He3LEN2KK2Hj2l0S2HK3LEN2Hj3HltS2HK3LEN2Hj4Hge2S2AB2HK3LEN2Hp2Hr3HprS2HK3LEN2RcS2HK3LEN4Hlt21HS2HK3LEN1HS2AB2HK2Hp2Hr3Hpr3LENS2HK3LENS2HK3LEN3Hge4Hlt2S2HK3Hpr3LENS2HK2Hp2Hr3Hpr3LEN2KKS2HK2He3LENS2HK2Hp3LENS2HK3LENS2AB2HK2Hp2Hr3Hpr3LENFS2AB2HK2Hp2Hr3Hpr3LENS2HK3LEN".
induction K as [K IH] using lt_wf_ind; intros c p r e m1 bs Q x15 x16 HK Hc ARR FIL LEN MI MU WM HQ Hp Hr [q4 Hq4] Hpr He;
      assert (Rc : (0 <= c < 256)%Z) by (subst c; apply Z.mod_pos_bound; lia).
    mst p 8%nat ltac:(symmetry; apply le8_bcast; lia).
    mst (p + 8)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
    mst (p + 16)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
    mst (p + 24)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
    zstep. zstep. zstep.
    if_cases KK; zify_cond KK.
    - (* [comment removed for export] *)
      replace (A + p + 32)%Z with (A + (p + 32))%Z by lia.
      replace (r + -32)%Z with (r - 32)%Z by lia.
      eapply (IH (Z.to_nat (r - 32)) ltac:(lia) c (p + 32)%Z (r - 32)%Z e _ _ _ x15 x16 eq_refl Hc ARR); try OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try lia.
      2:{ exists (q4 - 8)%Z. lia. }
      intros j Hj.
      destruct (Z_lt_le_dec j p) as [Hlt|Hge]. { left; left; left; left. apply HQ. lia. }
      destruct (Z_lt_le_dec j (p + 32)) as [Hlt2|Hge2]. 2:{ left; left; left; left. apply HQ. lia. }
      assert (D : ((p <= j < p + 8 \/ p + 8 <= j < p + 16) \/ (p + 16 <= j < p + 24 \/ p + 24 <= j < p + 32))%Z) by lia.
      destruct D as [[?|?]|[?|?]]; [left; left; left; right| left; left; right| left; right| right]; lia.
    - fin_with ltac:(intros j Hj; destruct (Z_lt_le_dec j p); [repeat left; apply HQ; lia|];
                      destruct (Z_lt_le_dec j (p + 32)); [|repeat left; apply HQ; lia]; disj_lia).
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  Lemma memset_body : forall junk,
    rw_cells usegs m A [CB (Z.to_nat n) junk] ->
    evt usegs POST (ST 0x1b640 m a1 a2 a3 a4 a5 a6).
  Proof using AB MI0.
    intros junk DST. pose proof MI0 as MI.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (zr_word a1) as R1. unfold inr64 in R1.
    remember (bv_unsigned a1 mod 256)%Z as c eqn:Hc.
    Local Ltac2 Set LiaHints.tbl := fun () => "01F0>11257553070.6211282918751.5511282918751.5611282918751.6311282918751.6411282918751.6711581494688.7713340421078.7414792234654.6514922085718.5214939502101.6115061790518.5615730339569.6117306419388.5218433389101.4218459507902.6618685696854.6119459610656.7419934346585.652004936736.77 21703262954.7523148063281.642472022896.62 2597469152.76 26838309408.7327768026206.5128704070102.6529306001122.7629437520746.7429588359186.6430572607345.6433774834522.543450621453.65 34723770152.653479334413.56 3488604886.70 3488604889.65 35214167689.7635214167690.7535483189910.623746152322.62 3746152322.63 3746152322.64 3746152322.66 37990331569.643914633127.49 40360039357.6540658349290.7540906124225.5241415944133.5442892005334.62437180346.53  4464661664.77 45401415882.6448868474571.5649105470880.7451541114560.7351800804714.7552862258502.6054410452520.6255358809119.5457736628310.6258544938066.6559308586377.5159586081466.7560723875015.6260871395060.6561472317202.6361782620778.7563411420139.5663455219786.706347338586.74 6358519893.62 6358521035.61 64834235857.5264988078826.7465152200624.6165408487657.5265866180128.7766370264865.5167409372242.6467642825125.548210661929.65 8321262001.61 903013489.53  903013489.60  00000M00^00o01N01m02X02]03203;03F03G03L03i04404504=04Z04_05<05A05F05c06406906>06?06D06O06T06Y07607A07V07o08C08`09409509609S09[09c09k0:30:P0:[0:`0:e0;00;50;R0;]0;b0<?0<J0<O0<P0<U0<i0=70=E0=b0=g0>50>:0>K0>l0?10?60?;0?R0?k0@D0@`0@k0A00AP0A[0A`0Ak0B00B50B60BS0B^0C3S2AB2R12K32Rk3Hq43Rn43LEN3K25S2R12K33LEN2K72HjS2R12K33LEN2K92HjS2AB2R12K32K92Rk3Rn43LEN3K9'2HjS2AB2R12K32K92Rk3Rn43LEN3K252HjS2AB2R12K02K92Rk3Hq43Rn43K253Rk43LEN3K322HjS3LENS2AB2R12K02Rk3LEN3Rk4S3Rn43LENS2AB3LEN2K3FS3LENS2AB2R12K32Rk3Hq43Rn43K9'3LENS2AB2K33LENSS3LEN2RkS2AB2R12K32Rk3Hq43Rn43K9'3LENS3LENS2AB2R12K02Rk3Rn43Rk43LEN3K32S3LENS3LENS2AB2R12K32Rk3Hq43Rn43K253LENS2AB2R12K32Rk3LENS3LENS3LENFS3LENS2R12K33LENS3LENS3LENS2AB2R12K32Rk3Hq43Rn43K253LENS2AB2K03LENS2AB2R12K02Rk3Rk43LENS2AB2R12K02Rk3Hq43Rk43LENS2AB2R12K33LEN2K92RkS2AB2R12K32Rk3Hq43Rn43K253LENS2AB2R12K33LEN2K92RkFFS2AB2R12K32Rk3Hq43Rn43K253LENS2Rc3LENS2Rc3LENS2Rc3LENS2Rc3LENS2AB2R12K32Rk3Hq43Rn43K253LENS2AB3LEN2K0S3LENS3LENS2AB2K33LENS3LENS2AB2R12K32Rk3Hq43Rn43K253LENS2AB3LEN2K7S3LENS2AB2R12K32Rk3Hq43Rn43K253LENS2AB2K03LENS3LENFS3LENS2AB2R12K33LEN2K92RkS2AB2K02Rk3LENS2R13LEN2K32HjS2AB2R12K32Rk3Hq43Rn43K253LENS3LENS2R13LEN2K02HjS3LENS2AB2R12K32Rk3LENS2AB2R12K02Rk3Hq43Rn43K253Rk43LENS3LENS3LENS3LENS2AB2R12Hc2Rc2K33LEN2RkS2AB2R12K32Rk3Rn43K9'3LENS2AB2R12K32Rk3Rn43K9'3LENS2AB2R12K32K92Rk3Hq43Rn43LENS2AB2K33LENS3LENS2AB2R12K32K92Rk3Hq43Rn43LEN3K9'S2AB2K03LENS3LENS2AB2K03LENS3LENS3LENFS2AB2R12K32Rk3Hq43Rn43K9'3LENS2AB2K73LENS2AB2R12K32K93Rn43LEN".
assert (Rc : (0 <= c < 256)%Z) by (subst c; apply Z.mod_pos_bound; lia).
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as ARR.
    pose proof (rw_cells_CB_length _ _ _ _ _ DST) as LEN.
    pose proof (filled_init (Z_to_bv 8 c) junk) as FIL.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0. { fin. }
    assert (MF : ms_facts A n 0 1) by (unfold ms_facts; lia).
    pose proof (ms_store_ok usegs _ A n _ 0 1 a0 ARR LEN MF (eq_sym (Z_to_bv_plus0 a0))) as SOK.
    zstep. ms_arr_store MF ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep. zstep. mst (n - 1)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep. if_cases K3; zify_cond K3. { fin. }
    mst 1%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    mst 2%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep.
    mst (n - 3)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    mst (n - 2)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep. if_cases K7; zify_cond K7. { fin. }
    mst 3%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep.
    mst (n - 4)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep. if_cases K9; zify_cond K9. { fin. }
    (* [comment removed for export] *)
    zstep. zstep.
    setreg 16%Z (Z_to_bv 64 (c * 2^56)) ltac:(apply Z_to_bv_eqm; rewrite Z.shiftl_mul_pow2 by lia; subst c; OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    zstep. zstep.
    remember (Z.land (bv_swrap 32 (0 - A) mod 18446744073709551616) 3) as k eqn:Hk.
    assert (Rk : (0 <= k < 4 /\ (A + k) mod 4 = 0)%Z).
    { subst k. change 3%Z with (2^2 - 1)%Z. rewrite zb_land_mask by lia.
      unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
      change (2 ^ (Z.of_N 32 - 1))%Z with (2^31)%Z. change (2 ^ Z.of_N 32)%Z with (2^32)%Z.
      OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
    clear Hk.
    zstep. zstep. zstep. zstep. zstep.
    change 18446744073709551612%Z with (2^64 - 2^2)%Z. rewrite land_align_down by lia.
    remember (n - k - (n - k) mod 2^2)%Z as n4 eqn:Hn4.
    assert (Rn4 : (exists q, n4 = 4 * q)%Z /\ (n - k - 3 <= n4 <= n - k)%Z).
    { split. { exists ((n - k) / 4)%Z. subst n4. OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. } subst n4. OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
    clear Hn4. destruct Rn4 as [[q4 Hq4] Rn4].
    zstep. setreg 12%Z (Z_to_bv 64 (c * BC4)) ltac:(unfold BC4; brute256 c Rc).
    (* [comment removed for export] *)
    mst k 4%nat ltac:(symmetry; apply le4_bcast; lia).
    zstep. mst (k + n4 - 4)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    zstep. if_cases K9'; zify_cond K9'. { fin. }
    mst (k + 4)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + 8)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    zstep.
    mst (k + n4 - 12)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + n4 - 8)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    zstep. if_cases K25; zify_cond K25. { fin. }
    mst (k + 12)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + 16)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + 20)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + 24)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    (* [comment removed for export] *)
    zstep.
    remember (Z.land (A + k) 4) as k4 eqn:Hk4.
    assert (Rk4 : ((k4 = 0 \/ k4 = 4) /\ (A + k + k4 + 24) mod 8 = 0)%Z).
    { subst k4. rewrite land4_of_aligned by lia. OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
    clear Hk4.
    zstep. zstep. zstep.
    mst (k + n4 - 28)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + n4 - 24)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + n4 - 20)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + n4 - 16)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    zstep. if_cases K32; zify_cond K32. { fin. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. setreg 12%Z (Z_to_bv 64 (c * BC8)) ltac:(unfold BC4, BC8; brute256 c Rc).
    zstep.
    replace (A + k + (k4 + 24))%Z with (A + (k + k4 + 24))%Z by lia.
    eapply (memset_loop _ c (k + k4 + 24) _ (k + n4 - 28) _ _ _ _ _ eq_refl Hc ARR); try OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try lia.
    exists (q4 - Z.div k4 4 - 6)%Z. lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Proofs.

Lemma memset_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte),
  rw_cells usegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  mem_inv usegs m ->
  evt usegs (memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b640) fc None m (seg_rom usegs)).
Proof.
  intros until junk. intros DST MI.
  eapply memset_body; [exact MI | | exact DST].
  pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
  pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R. cbn. Local Ltac2 Set LiaHints.tbl := fun () => "0010>52736856165.39000005S1B1R".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
