(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StrwF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope bv_scope.
Section CANSEC1. Context {rc : runConstT}.
End CANSEC1.
Ltac with_arr tac :=
lazymatch goal with
| ARR : u8arr ?segs ?m ?A ?bs, FIL : filled ?cb ?bs _, LEN : length ?bs = _ |- _ => tac segs ARR FIL LEN A cb
end.
Ltac brute256 c Rc :=
first [ apply word_eq_of_eqb | apply Z.eqb_eq | idtac ];
repeat match goal with H : context [c] |- _ => tryif constr_eq H Rc then fail else clear H end;
revert c Rc; apply brute256_ok; vm_compute; reflexivity.
Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Lemma land4_of_aligned : forall x, (0 <= x)%Z -> (x mod 4 = 0)%Z -> Z.land x 4 = (x mod 8)%Z.
Proof.
intros x Hx H4.
transitivity (Z.land (x mod 8) 4).
{ change 8%Z with (2^3)%Z. Local Ltac2 Set LiaHints.tbl := fun () => "0020>10157577708.1829784465626.4 00000<00=S2H41H2H02H5S".
rewrite <- Z.land_ones by lia. change (Z.ones 3) with 7%Z.
rewrite <- Z.land_assoc. reflexivity. }
assert (R : (x mod 8 = 0 \/ x mod 8 = 4)%Z) by (Z.div_mod_to_equations; lia).
destruct R as [R|R]; rewrite R; reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition memset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(a0 a1 a2 : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ rw_cells bsegs m' (bv_unsigned a0)
[CB (Z.to_nat (bv_unsigned a2)) (repeat (Z_to_bv 8 (bv_unsigned a1 mod 256)) (Z.to_nat (bv_unsigned a2)))].
Section Proofs.
Variables (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Hypothesis MI0 : mem_inv bsegs m.
Hypothesis AB : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 <= 2^64 /\ 0 <= bv_unsigned a2 < 2^64)%Z.
Hypothesis RR : rng RNG (bv_unsigned a0) (bv_unsigned a2).
Notation A := (bv_unsigned a0).
Notation n := (bv_unsigned a2).
Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
Notation POST := (memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m).
Notation ST pc mm x11 x12 x13 x14 x15 x16 :=
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
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
Lemma memset_loop : forall (K : nat) (c p r e : Z) (m1 : word -> option byte) (bs : list byte) (Q : Z -> Prop)
(x15 x16 : word),
Z.to_nat r = K ->
c = (bv_unsigned a1 mod 256)%Z ->
u8arr bsegs m1 A bs -> filled (Z_to_bv 8 c) bs Q -> length bs = Z.to_nat n ->
mem_inv bsegs m1 -> munch W m m1 -> wmono bsegs m m1 ->
(forall j, (0 <= j < p \/ e <= j < n) -> Q j)%Z ->
(0 <= p)%Z -> (32 <= r)%Z -> (exists q, r = 4 * q)%Z -> (p + r <= n)%Z -> (e + 28 <= p + r)%Z ->
evtF bsegs RNG POST (ST 0x9311c m1 (Z_to_bv 64 (A + p)) (Z_to_bv 64 (c * BC8)) (Z_to_bv 64 31) (Z_to_bv 64 r) x15 x16).
Proof using AB RR.
Local Ltac2 Set LiaHints.tbl := fun () => "00R0>11065392636.6711283365893.7118433022073.6319932234086.6720943972177.6722433216478.7923620033955.7225332637742.6726130493174.7230536993111.6632466410974.7832567987354.7032570090182.7132572771458.7032574867780.7134198808638.663746152322.68 37675369182.783999782563.72 40139300643.7243587764574.7845380309975.6647638617054.7952488055643.7153305394057.6757932427401.6759667368592.6761508843596.6763265100781.7165822950878.7968607035491.678208580118.67 867403351.66  8690906023.67 00000I00V00^00_00g00o01901D01R01k02=02J02h03703G03\03g04=04L04V04h05=05E05V05b06706B06M06_06g07<07=07R07ZS2HK2Hp2Hr3Hq43Hpr3LEN2KKS2HK3LEN1l2l0S2HK3LENFS2HK3LENS2HK3LENS2HK3LEN1HS2HK3LEN2KKS2HK3LEN3Hge1HS2AB2HK2Hp2Hr3Hq43Hpr3LENS2HK2Hp2Hr3Hpr3LENS2HK3LEN2Hj1lS2HK2Hp2Hr3Hq42He3LEN2KK2Hj2l0S2HK3LEN2Hj3HltS2HK3LEN2Hj4Hge2S2AB2HK3LEN2Hp2Hr3HprS2HK3LEN2RcS2HK2Hp2Hr3Hq43Hpr3LENS2HK3LEN4Hlt21HS2HK3LEN1HS2HK2Hp2Hr3Hpr3LENS2AB2HK2Hp2Hr3Hpr3LENS2HK3LENS2HK3LEN3Hge4Hlt2S2HK3Hpr3LENS2HK2Hp2Hr3Hpr3LEN2KKS2HK2He3LENS2HK2Hp3LENS2HK3LEN2Hp2Hr3HprS2HK3LENS2AB2HK2Hp2Hr3Hpr3LENFS2AB2HK2Hp2Hr3Hpr3LENS2HK3LEN".
induction K as [K IH] using lt_wf_ind; intros c p r e m1 bs Q x15 x16 HK Hc ARR FIL LEN MI MU WM HQ Hp Hr [q4 Hq4] Hpr He;
assert (Rc : (0 <= c < 256)%Z) by (subst c; apply Z.mod_pos_bound; lia).
mst p 8%nat ltac:(symmetry; apply le8_bcast; lia).
mst (p + 8)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
mst (p + 16)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
mst (p + 24)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
zstep. zstep. zstep.
if_cases KK; zify_cond KK.
-
replace (A + p + 32)%Z with (A + (p + 32))%Z by lia.
replace (r + -32)%Z with (r - 32)%Z by lia.
eapply (IH (Z.to_nat (r - 32)) ltac:(lia) c (p + 32)%Z (r - 32)%Z e _ _ _ x15 x16 eq_refl Hc ARR); try eassumption; try lia.
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
rw_cells bsegs m A [CB (Z.to_nat n) junk] ->
evtF bsegs RNG POST (ST 0x93044 m a1 a2 a3 a4 a5 a6).
Proof using AB MI0 RR.
intros junk DST. pose proof MI0 as MI.
pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM.
pose proof (zr_word a1) as R1. unfold inr64 in R1.
remember (bv_unsigned a1 mod 256)%Z as c eqn:Hc.
Local Ltac2 Set LiaHints.tbl := fun () => "01\0>11257553070.6511282918751.5811282918751.5911282918751.6611282918751.6711282918751.7011447729963.7611581494688.8013340421078.7714245770306.9314792234654.6814922085718.5514939502101.6415061790518.5915730339569.6415838603381.9917306419388.5518433389101.4518459507902.6918461681646.6718685696854.6419459610656.7719934346585.682004936736.80 20213419008.7621378083198.6721703262954.7823148063281.6724532755473.672472022896.65 25390038272.7925764297280.752597469152.79 26838309408.7627768026206.5428606789726.7628704070102.6829306001122.7929437520746.7729588359186.6730572607345.6730940621632.7933821124958.7734191062942.773450621453.68 34723770152.683479334413.59 3488604886.73 3488604889.68 35214167689.7935214167690.7835483189910.6536061609569.663746152322.65 3746152322.66 3746152322.67 3746152322.69 37990331569.6738487902577.663914633127.52 3959601585.87 40360039357.6840658349290.7840906124225.5541415944133.5742892005334.65437180346.56  4464661664.80 45401415882.6746680011423.8046690931063.7549105470880.7750998811297.6451541114560.7651800804714.7852862258502.6355358809119.5756775580097.6557519391424.7657736628310.6558544938066.6858990801950.6859308586377.5459586081466.7860395700446.7760723875015.6560736276766.7660871395060.6861472317202.6661782620778.7862354123392.7962728516544.7963455219786.736347338586.77 6358519893.65 6358521035.64 64834235857.5564988078826.7765152200624.6465866180128.8065946320414.7766370264865.5467409372242.6767642825125.578210661929.68 8321262001.64 903013489.56  903013489.63  00000M00^00o01N01m02X03103603K03g04004;04<04A04^05>05I05J05R05Z06706<06Y06^07807@07E07b07j08;08U08g08l09109209R09W09b09g09l0:I0:c0;=0;W0;l0<E0<Y0=60=J0=K0=L0=i0>10>90>A0>I0>Q0>n0?60?A0?W0?\0?a0?l0@10@N0@Y0@^0A;0AC0AW0A\0Ag0Ah0Am0BA0BO0BZ0C70CT0CY0Ca0Co0D40DN0D_0E90EZ0E_0Ed0F>0FX0Fo0GH0Ga0H=0HH0HM0Hm0I20IL0IW0I\0Ia0Ib0J?0JJ0J_S2AB2R12K32Rk3Hq43Rn43LEN3K25S2R12K33LEN2K72HjS2R12K33LEN2K92HjS2AB2R12K32K92Rk3Rn43LEN3K9'2HjS2AB2R12K32K92Rk3Rn43LEN3K252HjS2AB2R12K02K92Rk3Hq43Rn43K253Rk43LEN3K322HjS2AB2K03LEN1H2H02H42H52H9S3LENS2AB2R12K02Rk3LEN3Rk4S2AB2K02Rk3LEN1H2H02H42H52H9S3Rn43LENS2AB3LEN2K3FS3LENS2AB2R12K32Rk3Hq43Rn43K9'3LENS2AB2K03LEN2H42H52H93H103H143H19S2AB2K33LENSS3LEN2RkS2K33LENS2AB2R12K32Rk3Hq43Rn43K9'3LENS3LENS2AB2R12K02Rk3Rn43Rk43LEN3K32S3LENS2R12K32Rk3Hq43Rn43K9'3LENS3LEN2K3S3LENS2AB2R12K32Rk3Hq43Rn43K253LENS2K73LENS2AB2R12K32Rk3LENS2R12K32Rk3Hq43Rn43K253LENS2R12K32K93Rn43LENS3LENS3LENFS2AB2R12K32K92Rk3Hq43Rn43LEN3K9'S3LENS2R12K33LENS3LENS3LENS2AB2R12K32Rk3Hq43Rn43K253LENS2R12K32Rk3Hq43Rn43K253LENS2R12K32Rk3Hq43Rn43K253LENS2R12K32Rk3Hq43Rn43K253LENS2AB2R12K02Rk3Rk43LENS2AB2R12K02Rk3Hq43Rk43LENS2AB2R12K33LEN2K92RkS2AB2R12K32Rk3Hq43Rn43K253LENS2AB2R12K33LEN2K92RkFFS2AB2R12K32Rk3Hq43Rn43K253LENS2K33LENS2Rc3LENS2Rc3LENS2Rc3LENS2Rc3LENS2AB2R12K32Rk3Hq43Rn43K253LENS2K33LENS2AB3LEN2K0S2AB2K03LEN1H2H02H42H5S3LENS3LENS2AB2K33LENS3LENS2AB2R12K32Rk3Hq43Rn43K253LENS2AB3LEN2K7S3LENS2AB2R12K32Rk3Hq43Rn43K253LENS3LEN2H0S2AB2R12K33LEN2K92RkS3LENS2AB3LEN2K0FS3LENS2AB2R12K33LEN2K92RkS2R13LEN2K32HjS2AB2K03LENS2AB2R12K32Rk3Hq43Rn43K9'3LENS2AB2R12K32Rk3Hq43Rn43K253LENS3LENS3LEN2K7S2R13LEN2K02HjS3LENS2R12K32Rk3Hq43Rn43LEN3K25S2AB2R12K32Rk3LENS2R12K32Rk3Hq43Rn43K9'3LENS2AB2R12K02Rk3Hq43Rn43K253Rk43LENS3LENS3LENS2R12K32Rk3Hq43Rn43K253LENS2R12K32Rk3Hq43Rn43K253LENS2AB2R12Hc2Rc2K33LEN2RkS2AB2R12K32Rk3Rn43K9'3LENS2AB2R12K32Rk3Rn43K9'3LENS2AB2R12K32K92Rk3Hq43Rn43LENS2AB2K33LENS3LENS2AB2R12K32K92Rk3Hq43Rn43LEN3K9'S3LENS2R12K32Rk3Hq43Rn43K253LENS2AB2K03LENS3LENS3LENFS2AB2R12K32Rk3Hq43Rn43K9'3LENS2AB2K73LENS2AB2R12K32K93Rn43LEN".
assert (Rc : (0 <= c < 256)%Z) by (subst c; apply Z.mod_pos_bound; lia).
pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as ARR.
pose proof (rw_cells_CB_length _ _ _ _ _ DST) as LEN.
pose proof (filled_init (Z_to_bv 8 c) junk) as FIL.
zstep. if_cases K0; zify_cond K0. { fin. }
assert (MF : ms_facts A n 0 1) by (unfold ms_facts; lia).
pose proof (ms_store_ok bsegs _ A n _ 0 1 a0 ARR LEN MF (eq_sym (Z_to_bv_plus0 a0))) as SOK.
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
zstep. zstep.
setreg 16%Z (Z_to_bv 64 (c * 2^56)) ltac:(apply Z_to_bv_eqm; rewrite Z.shiftl_mul_pow2 by lia; subst c; Z.div_mod_to_equations; lia).
zstep. zstep.
remember (Z.land (bv_swrap 32 (0 - A) mod 18446744073709551616) 3) as k eqn:Hk.
assert (Rk : (0 <= k < 4 /\ (A + k) mod 4 = 0)%Z).
{ subst k. change 3%Z with (2^2 - 1)%Z. rewrite zb_land_mask by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ (Z.of_N 32 - 1))%Z with (2^31)%Z. change (2 ^ Z.of_N 32)%Z with (2^32)%Z.
Z.div_mod_to_equations. lia. }
clear Hk.
zstep. zstep. zstep. zstep. zstep.
change 18446744073709551612%Z with (2^64 - 2^2)%Z. rewrite land_align_down by lia.
remember (n - k - (n - k) mod 2^2)%Z as n4 eqn:Hn4.
assert (Rn4 : (exists q, n4 = 4 * q)%Z /\ (n - k - 3 <= n4 <= n - k)%Z).
{ split. { exists ((n - k) / 4)%Z. subst n4. Z.div_mod_to_equations. lia. } subst n4. Z.div_mod_to_equations. lia. }
clear Hn4. destruct Rn4 as [[q4 Hq4] Rn4].
zstep. setreg 12%Z (Z_to_bv 64 (c * BC4)) ltac:(unfold BC4; brute256 c Rc).
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
zstep.
remember (Z.land (A + k) 4) as k4 eqn:Hk4.
assert (Rk4 : ((k4 = 0 \/ k4 = 4) /\ (A + k + k4 + 24) mod 8 = 0)%Z).
{ subst k4. rewrite land4_of_aligned by lia. Z.div_mod_to_equations. lia. }
clear Hk4.
zstep. zstep. zstep.
mst (k + n4 - 28)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + n4 - 24)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + n4 - 20)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
mst (k + n4 - 16)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
zstep. if_cases K32; zify_cond K32. { fin. }
zstep. zstep. zstep. zstep. setreg 12%Z (Z_to_bv 64 (c * BC8)) ltac:(unfold BC4, BC8; brute256 c Rc).
zstep.
replace (A + k + (k4 + 24))%Z with (A + (k + k4 + 24))%Z by lia.
eapply (memset_loop _ c (k + k4 + 24) _ (k + n4 - 28) _ _ _ _ _ eq_refl Hc ARR); try eassumption; try lia.
exists (q4 - Z.div k4 4 - 6)%Z. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Proofs.
#[using="Type"] Lemma memset_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte),
rw_cells bsegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
mem_inv bsegs m ->
rng RNG (bv_unsigned a0) (bv_unsigned a2) ->
evtF bsegs RNG (memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x93044) fc None m (seg_rom bsegs)).
Proof.
intros until junk. intros DST MI RR.
eapply memset_body; [exact MI | | exact RR | exact DST].
pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R. cbn. Local Ltac2 Set LiaHints.tbl := fun () => "0010>52736856165.42000005S1B1R".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC2.
