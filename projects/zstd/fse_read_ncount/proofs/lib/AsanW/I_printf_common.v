(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import StrFun Stdio_pure.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg RtCells ShadowTac F_irt F_rip I_printf_lib.
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
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.
Local Ltac mem_after_store ::= cbv beta; try rewrite le1_unsigned8; mem_after_store_fast.
Section CANSEC1. Context {rc : runConstT}.
Section PC.
Variables (RNG : footprint)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
(FMT : Z) (fstr : list byte).
Hypothesis MI : mem_inv asegs m.
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis LO : (lo <= bv_unsigned sp - 2320)%Z.
Hypothesis KLO : (KHIGH <= lo)%Z.
Hypothesis GOT : rt_got m.
Hypothesis SHB : rt_shbase m.
Hypothesis A1 : a1 = Z_to_bv 64 FMT.
Hypothesis FB : bytes_at asegs m FMT (fstr ++ [Z_to_bv 8 0]).
Hypothesis NOZ : Forall (fun b : byte => bv_unsigned b <> 0%Z) fstr.
Notation L := (Z.of_nat (length fstr)).
Hypothesis FL : (1 <= L <= 62)%Z.
Hypothesis FIMG : (0x10000 <= FMT /\ FMT + L + 1 <= 0x5f7000)%Z.
Notation SLO := (shad (FMT - 64))%Z.
Notation SHI := (shad (FMT + L + 64))%Z.
Hypothesis FZ : shadow_bytes m SLO SHI (fun _ => 0%Z).
Hypothesis RI : rng_aimg RNG.
Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
Hypothesis RSHF : rng RNG SLO (SHI - SLO).
Notation W := [(bv_unsigned sp + -2320, bv_unsigned sp)]%Z.
Notation SAVES := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Notation PAT := 12297829382473034410%Z.
Definition INV (mc : word -> option byte) : Prop :=
rw_cells asegs mc (bv_unsigned sp + -104) SAVES
/\ (exists j0, rw_cells asegs mc (bv_unsigned sp + -2240) [CB 8 j0; C8 (Z_to_bv 64 (bv_unsigned sp + -120)); C8 a0])
/\ stk asegs mc (bv_unsigned sp + -2176) (bv_unsigned sp + -104)
/\ stk asegs mc lo (bv_unsigned sp + -2240)
/\ munch W m mc /\ wmono asegs m mc /\ mem_inv asegs mc /\ rt_got mc /\ rt_shbase mc.
Definition BL : Prop :=
(0 <= lo /\ lo <= bv_unsigned sp - 2320 /\ 17594333495296 <= lo /\ bv_unsigned sp < 2^64
/\ 65536 <= FMT /\ FMT + L + 1 <= 6254592 /\ 1 <= L <= 62
/\ 8192 <= Z.shiftr FMT 3 /\ Z.shiftr FMT 3 <= Z.shiftr (FMT + L) 3 /\ Z.shiftr (FMT + L) 3 <= Z.shiftr FMT 3 + 8 /\ Z.shiftr (FMT + L) 3 <= 795455
/\ shad (FMT - 64) = 2147450872 + Z.shiftr FMT 3 /\ shad (FMT + L + 64) = 2147450888 + Z.shiftr (FMT + L) 3)%Z.
#[using="m ST LO KLO FL FIMG"] Lemma BL_ok : BL.
Proof.
unfold BL. pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R.
destruct ST as (L0 & _). unfold KHIGH in KLO. Local Ltac2 Set LiaHints.tbl := fun () => "0020>29784531678.5662900827558.8400000100]SS2LO3KLO2FL4FIMG1R1H2H02H42H52H93H103H143H15".
rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF. Z.div_mod_to_equations. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Ltac hide_sec :=
change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in GOT;
change (?P) with (sf_hide P) in SHB; change (?P) with (sf_hide P) in FB;
change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO.
Ltac inv_open H := let j0 := fresh "j0" in destruct H as (FRT & (j0 & FRL) & STM & ST1 & MU1 & WM1 & MI1 & GOT1 & SHB1).
Ltac prep IV :=
inv_open IV;
let B := fresh "B" in pose proof BL_ok as B; unfold BL in B;
assert (RSTK' : rng RNG (bv_unsigned sp + -2320) 2320) by (eapply rng_sub'; [exact RSTK| lia]);
hide_sec.
#[using="lo ST LO KLO FB FL FIMG"] Lemma fmt_rd : forall mc (i : Z) b, mem_inv asegs mc -> munch W m mc ->
nth_error (fstr ++ [Z_to_bv 8 0]) (Z.to_nat i) = Some b -> (0 <= i)%Z ->
ov_read_bytes asegs mc (wa (FMT + i)) 1 = Some [b].
Proof.
intros mc i b MIc MUc Hn Hi. pose proof BL_ok as B; unfold BL in B.
eapply u8ro_read; [| exact Hn | exact Hi | reflexivity].
eapply bytes_at_transport; [exact FB | exact MUc |]. rewrite length_app; cbn [length disjoint_from]. Local Ltac2 Set LiaHints.tbl := fun () => "0010>56423662679.62000003S1B".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Ltac fmt_read i b Hn :=
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, MIc : mem_inv _ mc |- _ =>
let H := fresh "RD" in
pose proof (fmt_rd mc i b MIc MUc ltac:(rewrite nth_error_app1 by lia; exact Hn) ltac:(lia)) as H
end end.
Ltac prem :=
lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- mem_inv _ _ => first [assumption | eassumption | idtac "prem: mem_inv"; fail]
| |- context [bv_unsigned (Z_to_bv 64 _)] => rewrite !unsigned_lit by lia; prem
| |- stk _ _ _ _ => first [assumption | eassumption | idtac "prem: stk"; fail]
| |- find_byte _ _ = _ => first [eassumption | idtac "prem: find_byte"; fail]
| |- rw_cells _ _ _ _ => first [eassumption | idtac "prem: rw_cells"; fail]
| |- u8arr _ _ _ _ => first [eassumption | idtac "prem: u8arr"; fail]
| |- bytes_at _ _ _ _ => first [eassumption | first [apply flags_bytes | apply jzt_bytes | apply ccss_bytes | apply aefg_bytes | apply dioux_bytes | apply cs_bytes | apply csb_bytes | apply ss_bytes | idtac "prem: bytes_at"; fail]; assumption]
| |- Forall _ _ => first [exact flags_noz | exact jzt_noz | exact ccss_noz | exact aefg_noz | exact dioux_noz | exact cs_noz | exact csb_noz | exact ss_noz | assumption | idtac "prem: Forall"; fail]
| |- _ = Z_to_bv 64 _ => first [reflexivity | idtac "prem: eq"; fail]
| |- rng _ _ _ => first [ assumption | eapply rng_sub'; [exact RI | cbn; unfold sf_hide in *; lia] | eapply rng_sub'; [exact RSTK | unfold sf_hide in *; lia] | idtac "prem: rng"; fail ]
| |- ?g => unfold sf_hide in *; first [lia | cbv; discriminate | cbn; lia | idtac "prem: other" g; fail]
end.
Ltac br CC := let K := fresh "K" in if_cases K; zify_cond K; try (exfalso; clear -K CC; lia); [clear K].
#[using="fstr MI ST LO KLO GOT SHB A1 FB NOZ FL FIMG FZ RI RSTK RSHF"] Lemma L_entry : forall Q,
(forall mc dj, INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) [CB 40 dj] ->
forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
evtF asegs RNG Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp y9 y10 y11 y12 y13 y14 y15 y16 y17
(Z_to_bv 64 10) (Z_to_bv 64 FMT) (Z_to_bv 64 0x152a7) a2 y22 (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned sp + -2184))
(Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31)
F (Z_to_bv 64 0x45350) fc None mc (seg_rom asegs))) ->
evtF asegs RNG Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x4523c) fc None m (seg_rom asegs)).
Proof.
intros Q K.
pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof BL_ok as B; unfold BL in B.
Local Ltac2 Set LiaHints.tbl := fun () => "01P0?11447729958.11211805384353.73 1376782951.77  14240483175.77 14749644999.79 15047324418.78 15503951792.77 16075584200.75 17520533465.90 1839013063.74  1839144132.78  19416380902.76 19575182558.81 19628483873.75 19910263222.86 21522027824.78 22154060828.78 22933788594.73 22956501404.78 24115025141.85 24125015037.74 25756706588.77 27574837936.77 27578582448.89 27646807270.76 29413318759.77 29647033372.89 29784302302.84 30012542312.74 31230243308.90 31232667615.91 31435956124.78 3210808038.84  33246252700.76 33340954902.80 33340954905.85 33349831216.71 33351929361.74 33559621680.78 33563104048.85 34622740198.76 3467439280.77  34895115417.66 34964144796.78 36084089830.76 37172549197.65 3898298804.12  39611358640.77 40131048926.81 40472918502.76 42276887908.78 42831306615.79 43061432073.63 45059923527.68 45604399920.78 46122922854.75 48766660202.91 48833302825.74 48889933774.90 48905204221.91 48977348636.77 50446685169.91 50815571482.59 51622475952.77 52116139202.90 52512885532.77 54018539558.68 54131401776.76 57274386685.75 57388678684.77 57880736640.84 5811973867.84  59308628304.6  59308628433.6  59308628566.1  59308660947.76 59314873579.4  60183032240.78 60992364828.77 6132471369.78  6142306534.65  64911639964.79 65151722820.70 65788171676.85 6586366183.77  66066659640.98 66202263344.79 67515366756.91 67525256023.90 68481779868.79 7017134502.12  7611744875.88  7688076901.71  8386141284.78  9519331888.79  9822325092.78  00000100400500600700800900=00>00?00@00A00B00F00N00O00P00Q00R00U00X00Y00Z00[00\00]00^00_00`00a00b00c00d00e00m01501=01E01F01G01H01I01L01M01N01Q01W01X01Y01Z01[01\01_01`01a01b01c01d01e01f01g01h01l01m02502602902:02B02C02D02E02K02Q02U02\02f02g02h02k02l02m02n02o03003603703803903:03@03A03G03H03I03JFS1BSSSSSS2FLSSSSSS2FLS4FIMG1BSSSSS1BS1BSSSSSSSSFFSFSS4FIMG1BS4FIMG1BS4FIMG1BS4FIMG1BSSSSS1BSSS1BS1B2H0SSSSSS1BSSSSSFFSSS2LOSS4FIMG1BSS1BSS4FIMG1BSFSS1B2K1S1B2K2S2K3S2FL2E0S3NZ02K41HSSS1BSSSSSS1B2H0SFFSS1B2H0SS4FIMGSSS".
assert (RSTK' : rng RNG (bv_unsigned sp + -2320) 2320) by (eapply rng_sub'; [exact RSTK| lia]).
pose proof MI as MIc. pose proof FB as FBc. pose proof GOT as GOTc. pose proof SHB as SHBc. pose proof ST as ST0.
hide_sec.
subst a1.
carve_frame 104%nat ST0.
destruct (stk_split _ _ lo (bv_unsigned sp + -2176) _ ST0 ltac:(lia)) as [ST1 STM]. clear ST0.
carve_frame 40%nat ST1. carve_frame 24%nat ST1.
do 16 zstep. do 6 zstep. zstep.
call istrlen_spec; [ exact MIc | rewrite unsigned_lit by lia; exact FBc | exact NOZ | rewrite unsigned_lit by lia; eapply rng_sub'; [exact RI| lia] | ].
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m mc |- _ =>
pose proof (shadow_bytes_munch _ m mc _ _ _ FZ MUc ltac:(cbn [disjoint_from]; lia)) as FZ1 end end.
zstep. zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. { exfalso. clear - K1 B. lia. } clear K1.
zstep. zstep. if_cases K2; zify_cond K2. { exfalso. clear - K2 B. lia. } clear K2.
do 4 zstep. replace (L + FMT)%Z with (FMT + L)%Z by lia. do 6 zstep.
change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (ov_read8_zero asegs mc _ _ _ (2147450880 + Z.shiftr FMT 3 - (2147450880 + Z.shiftr FMT 3) mod 8)%Z FZ1
ltac:(clear -B; Z.div_mod_to_equations; lia) ltac:(clear -B; Z.div_mod_to_equations; lia) ltac:(intros; reflexivity)) as P1;
pose proof (ov_read8_zero asegs mc _ _ _ (2147450880 + Z.shiftr (FMT + L) 3 - (2147450880 + Z.shiftr (FMT + L) 3) mod 8)%Z FZ1
ltac:(clear -B; Z.div_mod_to_equations; lia) ltac:(clear -B; Z.div_mod_to_equations; lia) ltac:(intros; reflexivity)) as P2
end.
zs. zs. zs. fold_lits. zs. if_cases K3; zify_cond K3. { exfalso. clear - K3. lia. } clear K3 P1 P2.
do 3 zs.
destruct (nth_error fstr 0) as [c0|] eqn:E0. 2:{ exfalso. apply nth_error_None in E0. lia. }
assert (NZ0 : bv_unsigned c0 <> 0%Z) by (eapply (proj1 (Forall_forall _ _) NOZ); eapply nth_error_In; exact E0).
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m mc, MIc : mem_inv _ mc |- _ =>
pose proof (fmt_rd mc 0 c0 MIc MUc ltac:(rewrite nth_error_app1 by lia; exact E0) ltac:(lia)) as RD0; rewrite Z.add_0_r in RD0 end end.
zs. zs. if_cases K4; zify_cond K4. { exfalso. clear - K4 NZ0. pose proof (bv_unsigned_in_range 8 c0). cbn in *. lia. } clear K4 RD0.
do 17 zs.
eapply K. 2:{ exact FR0. }
split; [exact FR|]. split; [eexists; exact FR1|]. unfold sf_hide in *. repeat (split; [assumption|]). assumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Notation dcells1 :=
([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 18446744073709551615); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3)]) (only parsing).
Definition lregs (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 : word) (p aq : word) (y22 y28 y29 y30 y31 : word) :=
mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp y9 y10 y11 y12 y13 y14 y15 y16 y17
(Z_to_bv 64 10) p (Z_to_bv 64 0x152a7) aq y22 (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned sp + -2184))
(Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31.
#[using="FMT fstr ST LO KLO FL FIMG RSTK"] Lemma L_head : forall Q mc dcs p aq,
INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcs -> cells_size dcs = 40%nat ->
(forall mc', INV mc' -> rw_cells asegs mc' (bv_unsigned sp + -2216) dcells1 ->
forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
evtF asegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 p aq y22 y28 y29 y30 y31)
F (Z_to_bv 64 0x4537c) fc None mc' (seg_rom asegs))) ->
forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
evtF asegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 p aq y22 y28 y29 y30 y31)
F (Z_to_bv 64 0x45350) fc None mc (seg_rom asegs)).
Proof.
intros Q mc dcs p aq IV DIR SZ K. intros. unfold lregs. Local Ltac2 Set LiaHints.tbl := fun () => "00I0?12787773674.10214266346288.10315798567580.99 20318107824.10320318107824.10720828558108.10320828558108.1072228777008.99  24763131158.97 38055958391.10347295305927.10347462902623.95 48294851690.10248296161692.10350815571482.91 53506443062.97 54619488865.95 55232824277.95 5596483612.103 56740522854.98 5754159462.95  59325058538.10259325058538.10661125124458.1028281562544.103 00000400800<00@00G00K00R00V00]00a00e00l01001401;01B01K01T01X01\01c01g01n022026S2SZS2SZS2SZS2SZS2SZ2DLS2SZS2SZ2DLS2SZS2SZ2DLS2SZS2SZS2SZ2DLS2SZS2SZS2LO2SZS2SZ2DLS2SZ1B2DLS2SZ1B2DLS2SZS2SZS2SZ2DLS2SZS2SZ2DLS2SZS2SZ".
prep IV.
destruct (rw_cells_forget _ _ _ _ DIR) as [dj DJ]. rewrite SZ in DJ. clear DIR.
do 5 zs. do 5 zs.
destruct (u8arr_of_chunk _ _ _ _ DJ) as (dj2 & DA & DL). cbn in DL. clear DJ.
call imemset_specZ; [ exact MI1 | exact DA | rewrite DL; reflexivity | lia | lia | lia | cbv; discriminate | ].
match goal with H : u8arr asegs ?mc _ _ |- _ => rewrite ?unsigned_lit in H by lia;
apply rw_cells_of_u8arr in H; recell H 0%nat 1%nat (zcells0 : list cell); rename H into DIR end.
zs.
eapply K. 2:{ exact DIR. }
split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="lo ST LO KLO FB NOZ FL FIMG"] Lemma fmt_char : forall mc (i : Z), mem_inv asegs mc -> munch W m mc -> (0 <= i < L)%Z ->
exists b, nth_error fstr (Z.to_nat i) = Some b /\ bv_unsigned b <> 0%Z /\ (0 <= bv_unsigned b < 256)%Z /\
ov_read_bytes asegs mc (wa (FMT + i)) 1 = Some [b].
Proof.
intros mc i MIc MUc Hi.
destruct (nth_error fstr (Z.to_nat i)) as [b|] eqn:E. 2:{ exfalso. apply nth_error_None in E. Local Ltac2 Set LiaHints.tbl := fun () => "0040>10358064710.6121381470951.6235403344009.6159314955108.6000000400700>00GS2HiS1RS2FL2HiS2FL2Hi1E".
lia. }
exists b. split; [reflexivity|]. split.
{ eapply (proj1 (Forall_forall _ _) NOZ). eapply nth_error_In; exact E. }
split. { pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. }
eapply fmt_rd; [exact MIc | exact MUc | rewrite nth_error_app1 by lia; exact E | lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="lo ST LO KLO FB NOZ FL FIMG RI"] Lemma L_skip : forall Q mc (k : nat) (i : Z) aq,
mem_inv asegs mc -> munch W m mc -> (0 <= i)%Z -> (i + Z.of_nat k <= L)%Z ->
(forall j b, (Z.to_nat i <= j < Z.to_nat i + k)%nat -> nth_error fstr j = Some b -> bv_unsigned b <> 37%Z) ->
(forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
evtF asegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + (i + Z.of_nat k))) aq y22 y28 y29 y30 y31)
F (Z_to_bv 64 0x4537c) fc None mc (seg_rom asegs))) ->
forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
evtF asegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + i)) aq y22 y28 y29 y30 y31)
F (Z_to_bv 64 0x4537c) fc None mc (seg_rom asegs)).
Proof.
intros Q mc k. induction k as [|k IH]; intros i aq MIc MUc Hi Hk NP K; intros.
- specialize (K y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31).
rewrite Z.add_0_r in K. exact K.
- pose proof BL_ok as B; unfold BL in B. unfold lregs.
Local Ltac2 Set LiaHints.tbl := fun () => "00>0?16742176484.98 19522393435.85 21762809063.99 21772698328.98 27668080405.90 31572295838.11141250041896.93 46183404796.97 48822991312.98 48837994479.99 59308628304.4  59308628433.4  64689445906.93 66429145178.93 00000900@00A00B00F00J00Q00[00\00]00e00o013017S2Hi2Hk1BS2Hi2HkFFS2HkS2HkS2Hi2HkS2Hi2Hk2HjFFS3NP02K1S2NZ2RB2K2S2HkS2Hk".
destruct (fmt_char mc i MIc MUc ltac:(lia)) as (b & Hn & NZ & RB & RD).
assert (NP0 : bv_unsigned b <> 37%Z) by (eapply NP; [|exact Hn]; lia).
zs. zs. if_cases K1; zify_cond K1. { exfalso. clear -K1 NP0 RB. lia. }
zs. if_cases K2; zify_cond K2. { exfalso. clear -K2 NZ RB. lia. }
zs. zs. zs.
replace (FMT + i + 1)%Z with (FMT + (i + 1))%Z by lia.
eapply (IH (i + 1)%Z); [exact MIc | exact MUc | lia | lia | | ].
{ intros j b' Hj Hb'. eapply NP; [|exact Hb']. lia. }
intros. replace (i + 1 + Z.of_nat k)%Z with (i + Z.of_nat (S k))%Z by lia. apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition dirA_ok (c : Z) : Prop :=
find_byte c B_FLAGS = None /\ find_byte c B_JZT = None /\ (58 <= c < 256)%Z /\ c <> 108%Z /\ c <> 104%Z.
Definition intconv (c : Z) : Prop := c = 100%Z \/ c = 117%Z.
#[using="fstr"] Lemma cfacts : forall c, intconv c ->
dirA_ok c /\ find_byte c B_CCSS = None /\ find_byte c B_AEFG = None
/\ (exists ix, find_byte c B_DIOUX = Some ix) /\ (58 <= c < 256)%Z /\ c <> 109%Z /\ c <> 110%Z.
Proof. Local Ltac2 Set LiaHints.tbl := fun () => "00;0>13755265134.5429678350414.5431380799902.5439568913214.5444812789660.5448004958.54   57079046702.5464948207998.5467030413070.548212626589.54 9107345388.54 00000100200300400500600700800900:00;SSSSSSSSSFS".
intros c [-> | ->]; repeat split; try (cbv; reflexivity); try lia; eexists; cbv; reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition sconv (c : Z) : Prop := c = 115%Z.
#[using="fstr"] Lemma sfacts : forall c, sconv c ->
dirA_ok c /\ (58 <= c < 256)%Z /\ c <> 109%Z /\ c <> 110%Z
/\ find_byte c B_CCSS = Some 2%nat /\ find_byte c B_CS = None /\ find_byte c B_CSB = Some 1%nat /\ find_byte c B_SS = Some 0%nat.
Proof. intros c ->; repeat split; try (cbv; reflexivity); lia. Qed.
#[using="Type"] Lemma istrchr_res_none : forall A str c, find_byte c str = None -> istrchr_res A str c = 0%Z.
Proof. intros A str c H. unfold istrchr_res. rewrite H. reflexivity. Qed.
Notation dcellsA p bc :=
([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 18446744073709551615); C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 (p + 2));
C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 bc; CB 3 (repeat (Z_to_bv 8 0) 3)]) (only parsing).
#[using="ST LO KLO FB FL FIMG RI RSTK"] Lemma L_dirA : forall Q mc (i : Z) aq b37 bc,
INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcells1 ->
(0 <= i)%Z -> (i + 2 <= L)%Z ->
nth_error fstr (Z.to_nat i) = Some b37 -> bv_unsigned b37 = 37%Z ->
nth_error fstr (Z.to_nat (i + 1)) = Some bc -> dirA_ok (bv_unsigned bc) ->
(forall mc', INV mc' -> rw_cells asegs mc' (bv_unsigned sp + -2216) (dcellsA (FMT + i) bc) ->
forall y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
evtF asegs RNG Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp (Z_to_bv 64 (FMT + i)) (Z_to_bv 64 (bv_unsigned bc)) y11 y12 y13 y14 y15 y16 y17
(Z_to_bv 64 10) (Z_to_bv 64 (FMT + i + 2)) (Z_to_bv 64 0x152a7) aq (Z_to_bv 64 (FMT + i + 1)) (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned sp + -2184))
(Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31)
F (Z_to_bv 64 0x454f8) fc None mc' (seg_rom asegs))) ->
forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
evtF asegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + i)) aq y22 y28 y29 y30 y31)
F (Z_to_bv 64 0x4537c) fc None mc (seg_rom asegs)).
Proof.
intros Q mc i aq b37 bc IV DIR Hi HiL H37 E37 Hc HC K. intros. unfold lregs. Local Ltac2 Set LiaHints.tbl := fun () => "01O0?10351675204.10310489001451.11110497972204.11311879459221.11811879459221.12111879459222.11711879459223.11311879459223.11611879459224.11211879459226.11611888298910.11411888298910.11511888298910.11811888298910.11911888298910.12011888298910.12312561887685.10612785676515.12114266346288.11414665740598.10914793070390.10414793070390.10714935665936.10615798567580.11516742176484.11121764907231.11321772698328.11121848346821.1032228777008.115 27557538928.11728377667525.11828377667525.12128377667526.11728377667527.11328377667527.11628377667528.11228377667530.11629240271650.2  29717215540.11633115000181.11435405539723.10341247984776.10341247984776.10641250812073.10641250812718.10942476017083.10342476017083.10642478578074.10642478578205.10945373595996.11748294851691.11348296161692.11448822991312.11148831699927.11350103667030.1095068188992.112 5068188994.116 5068189005.118 5068189005.121 5068189006.117 5068189007.113 5068189007.116 5077028678.114 5077028678.115 5077028678.118 5077028678.119 5077028678.120 5077028678.123 50815571482.97 52687817718.10652991224336.1035596483612.122 59130343152.11359130343152.11659130343153.11759130343154.11859130343154.12159130343165.11659130343167.11259139312889.11459139312889.11559139312889.11859139312889.11959139312889.12059139312889.12359308628179.3  60076871025.10962554100401.10664669971924.11364669971924.11464669971924.11764669971924.11864669971924.11964669971924.1228281562544.122 00000400500600700800900:00;00<00=00>00?00@00A00B00C00D00E00F00G00K00O00P00Q00[00\00]00^00_00`00j01401>01H01R01\01f01j01k01l02402802<02@02D02L02T02\02d02e02f02g02h02i02j02k02l02m02n02o03003103203303403503603703;03<03=03>03?03@03A03B03C03D03E03F03G03H03I03J03K03R03S03T03U03V03W03X03Y03Z03[S2HiFFFFFFFFFFFFFFFSSSSS2CRS2CRSSS2Hi3HiL1BFFSSSS2Hi3HiL1BS2Hi3HiL1BS2Hi3HiL1BS2Hi3HiL1BS2Hi3HiL1BS2Hi3HiL1BS2Hi3HiL1BS2CCSSS2Hi3HiLS2HiS2HiS2HiS2HiS2Hi3HiLS2Hi3HiLS2Hi3HiLS2Hi3HiLSSSFFSFFFFFFFFFFFFFS2LOSSSFFFFFFFFFFFFFS2K02CCSSSSSSSSS".
prep IV.
destruct HC as (NF1 & NF2 & CR & N108 & N104).
pose proof (conj CR (conj N108 N104)) as CC.
fmt_read i b37 H37. zs. clear RD. cbv beta. rewrite E37. zs. br CC.
zs. fmt_read (i + 1)%Z bc Hc. zs. clear RD. cbv beta.
zs. br CC.
zs. br CC.
zs. zs. zs. br CC.
zs. fmt_read (i + 1)%Z bc Hc. zs. clear RD. cbv beta. zs. zs. zs.
call istrchr_spec; [ eassumption | apply flags_bytes; assumption | exact flags_noz | reflexivity | clear -CC; lia
| rewrite unsigned_lit by lia; eapply rng_sub'; [exact RI | cbn; lia] | ].
rewrite (istrchr_res_none _ _ _ NF1).
zs. zs. zs. br CC.
replace (FMT + (i + 1) + 1 + -1)%Z with (FMT + (i + 1))%Z by lia.
fmt_read (i + 1)%Z bc Hc. zs. clear RD. cbv beta. zs. zs. br CC.
zs. replace (FMT + (i + 1) + 1 + -1)%Z with (FMT + (i + 1))%Z by lia.
zs. fmt_read (i + 1)%Z bc Hc. zs. clear RD. cbv beta. zs. zs. br CC.
zs. zs. br CC.
zs. fmt_read (i + 1)%Z bc Hc. zs. clear RD. cbv beta. zs. zs. zs.
call istrchr_spec; [ eassumption | apply jzt_bytes; assumption | exact jzt_noz | reflexivity | clear -CC; lia
| rewrite unsigned_lit by lia; eapply rng_sub'; [exact RI | cbn; lia] | ].
rewrite (istrchr_res_none _ _ _ NF2).
fmt_read (i + 1)%Z bc Hc. zs. clear RD. cbv beta. zs. br CC.
zs. zs. br CC. zs. zs. br CC.
fmt_read (i + 1)%Z bc Hc. zs. clear RD. cbv beta. zs. zs. zs.
zs. br CC.
replace (FMT + (i + 1) + 1)%Z with (FMT + i + 2)%Z by lia. replace (FMT + (i + 1))%Z with (FMT + i + 1)%Z by lia.
eapply K. 2:{ match goal with H : rw_cells asegs _ (bv_unsigned sp + -2216) _ |- _ => exact H end. }
split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="ST LO KLO FL FIMG RI RSTK"] Lemma L_dirB : forall Q mc (i : Z) aq bc,
INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) (dcellsA (FMT + i) bc) ->
(0 <= i)%Z -> (i + 2 <= L)%Z -> intconv (bv_unsigned bc) ->
(forall mc' dcs', INV mc' -> rw_cells asegs mc' (bv_unsigned sp + -2216) dcs' -> cells_size dcs' = 40%nat ->
forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
evtF asegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + i + 2)) (Z_to_bv 64 (bv_unsigned aq + 8)) y22 y28 y29 y30 y31)
F (Z_to_bv 64 0x45348) fc None mc' (seg_rom asegs))) ->
forall y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
evtF asegs RNG Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp (Z_to_bv 64 (FMT + i)) (Z_to_bv 64 (bv_unsigned bc)) y11 y12 y13 y14 y15 y16 y17
(Z_to_bv 64 10) (Z_to_bv 64 (FMT + i + 2)) (Z_to_bv 64 0x152a7) aq (Z_to_bv 64 (FMT + i + 1)) (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned sp + -2184))
(Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31)
F (Z_to_bv 64 0x454f8) fc None mc (seg_rom asegs)).
Proof.
intros Q mc i aq bc IV DIR Hi HiL HC K. intros. Local Ltac2 Set LiaHints.tbl := fun () => "00V0?15798567580.10720828558108.10921537976752.10422098269854.10424800094436.10628235686975.10429228002099.11829239924756.10429240271650.99 29704818371.11829717215544.11029717215547.11229719312691.13031182322486.10833115000180.10634886800810.10840384252295.99 40723440083.10743164648726.12145373595996.11145373595996.11345510152889.12147027545905.10250357205755.10350359302899.12150815571482.90 5112668074.120 52912540651.10456173147160.10457020178110.99 59308628179.3  63837514828.13165247782060.10765562238940.10766363805625.10468278492694.1187826451026.99  8131073892.106 00000100200300700800900=00A00E00F00G00H00I00N00O00P00Q00R00S00T00U00V00W00X00Y00]00^00_00`00a00h00i00j00k00n00o010011SSFS2LOSSS2CRS2CRS2CRSSSSS1B1HSSSSSSSSSSSS2LOSSSSS2K02CCSSSS1BSSS".
prep IV.
destruct (cfacts _ HC) as (_ & NF3 & NF4 & (ix & HF) & CR & N109 & N110).
pose proof (conj CR (conj N109 N110)) as CC.
recell DIR 2%nat 1%nat [C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 4294967295)].
zs. change (sx32 (Z_to_bv 64 4294967295)) with (Z_to_bv 64 (-1)). zs. br CC.
zs. change (sx32 (Z_to_bv 64 4294967295)) with (Z_to_bv 64 (-1)). zs. br CC.
zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
zs. cbv beta. zs. zs. br CC. zs. zs. zs.
call istrchr_spec. all: prem.
rewrite (istrchr_res_none _ _ _ NF3).
zs. cbv beta. zs. br CC.
zs. zs. zs. zs. zs.
chunk_split DIR 8%nat DIR2. chunk_split DIR2 1%nat DIR3.
call_sp fgvs_spec. all: prem.
zs. zs. zs. br CC.
zs. cbv beta. zs. zs. br CC.
zs. zs. br CC. zs. br CC.
zs. zs. zs.
call istrchr_spec. all: prem.
rewrite (istrchr_res_none _ _ _ NF4).
zs. br CC.
zs. zs. zs. br CC. zs. zs. br CC. zs. zs. br CC.
zs.
chunk_join DIR DIR2. chunk_join DIR DIR3.
unfold lregs in K. eapply K. 2:{ exact DIR. } 2:{ reflexivity. }
split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Ltac norm_stk H tgt :=
lazymatch type of H with stk _ _ _ ?hi =>
replace hi with tgt in H by (cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; lia) end.
Notation POST := (printf_common_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).
#[using="ST LO KLO FB FL FIMG RI RSTK"] Lemma L_last : forall mc aq,
INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcells1 ->
forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
evtF asegs RNG POST (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + L)) aq y22 y28 y29 y30 y31)
F (Z_to_bv 64 0x4537c) fc None mc (seg_rom asegs)).
Proof.
intros mc aq IV DIR. intros. unfold lregs. Local Ltac2 Set LiaHints.tbl := fun () => "00g0?1376782955.99  14240483178.98 19416380903.95 20708443732.10220710540882.98 20713232492.10320713232492.99 22154060828.99 22956501404.99 24308966260.93 25756706588.96 27646807269.97 29250672709.89 29413318762.98 29717215541.98 31399080995.90 31435956124.10033246252700.98 33910734741.89 34622740197.97 34964144796.99 35941807962.91 36084089828.96 37170797037.91 37718656859.90 40379730232.93 40472918500.96 42276887908.96 42831306615.97 45373595996.99 46122922853.97 48977348636.98 5033361976.102 5035459134.98  5046279168.103 5046279168.99  50815571482.86 52512885532.97 54488094757.92 56228069995.10356228069995.99 56230894677.98 56232991827.10257020423743.90 57388678684.98 59314923118.2  60992364828.97 64911639964.1006586366186.98  67735273065.87 68481779868.99 8386141291.99  9496291338.98  9498388492.102 9822325098.98  00000100200300400500600700800900:00;00<00@00A00B00E00F00G00J00K00L00M00N00Q00R00S00T00U00V00W00X00Y00Z00[00\00]00a00b00e00f00g00h00i00j00k00n00o01001101501601701?01G01HSSSFFFFSSSSSS2FLSSS1BSSS1BSSSSS1BSSSSSSSSFFFFS2LOSS1BFFFFSSS1KSSSS2FLSSS4FIMG1BS4FIMG1BS".
prep IV.
assert (HL : nth_error (fstr ++ [Z_to_bv 8 0]) (Z.to_nat L) = Some (Z_to_bv 8 0)) by (rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia; reflexivity).
assert (CC : True) by exact I.
pose proof (fmt_rd mc L (Z_to_bv 8 0) MI1 MU1 HL ltac:(lia)) as RD.
zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC. zs. br CC.
zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC. zs.
zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
clear RD. zs. do 13 zs. zs. zs.
pose proof (stk_release _ _ _ _ _ ST1 FRL ltac:(lia)) as SK1. norm_stk SK1 (bv_unsigned sp + -2216)%Z.
pose proof (stk_release _ _ _ _ _ SK1 DIR ltac:(lia)) as SK2. norm_stk SK2 (bv_unsigned sp + -2176)%Z.
pose proof (stk_merge _ _ _ _ _ SK2 STM ltac:(lia)) as SK3.
pose proof (stk_release _ _ _ _ _ SK3 FRT ltac:(lia)) as SK4. norm_stk SK4 (bv_unsigned sp).
replace (bv_unsigned sp + -2320)%Z with (bv_unsigned sp - 2320)%Z in MU1 by lia.
finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="FMT MI ST LO KLO GOT SHB A1 FB NOZ FL FIMG FZ RI RSTK RSHF"] Theorem printf_common_int1 : forall pre b37 bc post,
fstr = pre ++ b37 :: bc :: post ->
Forall (fun b : byte => bv_unsigned b <> 37%Z) pre -> Forall (fun b : byte => bv_unsigned b <> 37%Z) post ->
bv_unsigned b37 = 37%Z -> intconv (bv_unsigned bc) -> post <> [] ->
evtF asegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x4523c) fc None m (seg_rom asegs)).
Proof.
intros pre b37 bc post EF NP1 NP2 E37 HC NE.
Local Ltac2 Set LiaHints.tbl := fun () => "00S0?14105795920.17415047277527.10820710540893.18620719526996.18823552344883.16124314867220.17726265415335.12427654620486.10627752260210.12427994577949.16128532548836.16129227258478.13929227258595.12429539222706.10833555826544.1243405560941.139 3405561056.124 37393454705.12438021105375.66 39203413114.19140599393995.1874115694607.124 41610801092.18745530951034.20548836336870.64 5035459121.186 5044183096.188 50815571482.17351077630375.19156221793875.18856230894682.18659308661201.16059314923118.3  59702536596.1129496291333.186 00000<00E00F00G00S00_00h01101:01F01R01[01d01m02602?02H02Q02V02b02k03403=03F03G03H03I03X03d03e03f04504<04H04VS3LEN3NE'2SZS3LEN3NE'FFS3LEN3NE'2SZS3LEN3NE'2SZS3LEN3NE'S3LEN3NE'S3LEN3NE'S3LEN3NE'2SZS3LEN3NE'2SZS3LEN3NE'S3LEN3NE'S3LEN3NE'S3LEN3NE'S3LEN3NE'S3LEN3NE'S3LEN3NE'S3LENS3LEN3NE'2HjS3LEN3NE'S3LEN3NE'S3LEN3NE'S3LEN3NE'SFFS2LO3LEN3NE'2SZS3LEN3NE'2HjFFS3LEN3NE'2SZ2E2S3NZ21KS3LEN3NE'2HjS3LEN3NE'2SZ1B".
assert (LEN : length fstr = (length pre + 2 + length post)%nat) by (rewrite EF, length_app; cbn; lia).
assert (NE' : (1 <= length post)%nat) by (destruct post; [congruence | cbn; lia]).
set (np := Z.of_nat (length pre)).
eapply L_entry. intros mc dj IV DIR. intros.
eapply (L_head _ mc [CB 40 dj]); [exact IV | exact DIR | reflexivity |]. clear mc dj IV DIR. intros mc IV DIR. intros.
replace (Z_to_bv 64 FMT) with (Z_to_bv 64 (FMT + 0)) by (f_equal; lia).
pose proof IV as IV'. destruct IV' as (_ & _ & _ & _ & MUc & _ & MIc & _).
eapply (L_skip _ mc (length pre) 0); [exact MIc | exact MUc | lia | lia | |].
{ intros j b Hj Hb. eapply (proj1 (Forall_forall _ _) NP1). eapply nth_error_In. rewrite EF, nth_error_app1 in Hb by lia. exact Hb. }
clear MUc MIc. intros. rewrite Z.add_0_l.
eapply (L_dirA _ mc np _ b37 bc); [exact IV | exact DIR | lia | lia | | exact E37 | | exact (proj1 (cfacts _ HC)) |].
{ rewrite EF. replace (Z.to_nat np) with (length pre) by lia. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. }
{ rewrite EF. replace (Z.to_nat (np + 1)) with (length pre + 1)%nat by lia. rewrite nth_error_app2 by lia.
replace (length pre + 1 - length pre)%nat with 1%nat by lia. reflexivity. }
clear mc IV DIR. intros mc IV DIR. intros.
eapply (L_dirB _ mc np); [exact IV | exact DIR | lia | lia | exact HC |].
clear mc IV DIR. intros mc dcs IV DIR SZ. intros. unfold lregs.
destruct (nth_error post 0) as [b2|] eqn:E2. 2:{ exfalso. apply nth_error_None in E2. lia. }
assert (H2 : nth_error fstr (Z.to_nat (np + 2)) = Some b2).
{ rewrite EF. replace (Z.to_nat (np + 2)) with (length pre + 2)%nat by lia. rewrite nth_error_app2 by lia.
replace (length pre + 2 - length pre)%nat with 2%nat by lia. exact E2. }
pose proof IV as IV'. prep IV'.
destruct (fmt_char mc (np + 2) MI1 MU1 ltac:(lia)) as (b2' & Hb2 & NZ2 & RB2 & RD2). rewrite H2 in Hb2. injection Hb2 as <-.
replace (FMT + np + 2)%Z with (FMT + (np + 2))%Z by lia.
zs. cbv beta. zs. assert (CC : True) by exact I. br NZ2.
eapply (L_head _ mc dcs); [exact IV | exact DIR | exact SZ |].
clear mc IV DIR SZ FRT FRL STM ST1 MU1 WM1 MI1 GOT1 SHB1 RD2. intros mc IV DIR. intros.
pose proof IV as IV'. destruct IV' as (_ & _ & _ & _ & MUc & _ & MIc & _).
eapply (L_skip _ mc (length post) (np + 2)); [exact MIc | exact MUc | lia | lia | |].
{ intros j b Hj Hb. eapply (proj1 (Forall_forall _ _) NP2). eapply nth_error_In with (n := (j - (length pre + 2))%nat).
rewrite EF, nth_error_app2 in Hb by lia.
replace (j - length pre)%nat with (S (S (j - (length pre + 2)))) in Hb by lia. exact Hb. }
intros. replace (np + 2 + Z.of_nat (length post))%Z with L by lia.
eapply L_last; [exact IV | exact DIR].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Variables (Sa : Z) (sstr : list byte) (RLO RHI : Z).
Hypothesis LAY : rt_layout m.
Hypothesis VAQ : rw_cells asegs m (bv_unsigned a2) [C8 (Z_to_bv 64 Sa)].
Hypothesis SEPV : (bv_unsigned sp <= bv_unsigned a2 /\ bv_unsigned a2 + 8 <= 2^64)%Z.
Hypothesis SSTR : bytes_at asegs m Sa (sstr ++ [Z_to_bv 8 0]).
Hypothesis SNOZ : Forall (fun b : byte => bv_unsigned b <> 0%Z) sstr.
Notation NS := (Z.of_nat (length sstr) + 1)%Z.
Hypothesis SEPS : (Sa + NS <= bv_unsigned sp - 2320 \/ bv_unsigned sp <= Sa)%Z.
Hypothesis APPS : app_blk Sa (Sa + NS).
Hypothesis SPOS : (0 < Sa)%Z.
Hypothesis USTR : unpoisoned m Sa (Sa + NS).
Hypothesis NSZ : (NS <= 2^40)%Z.
Hypothesis R1 : (RLO <= Sa /\ Sa + NS <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z.
Hypothesis WR1 : wr_at asegs m (shad RLO) (shad RHI - shad RLO).
Hypothesis RVA : rng RNG (bv_unsigned a2) 8.
Hypothesis RS : rng RNG Sa NS.
Hypothesis RSH1 : rng RNG (shad RLO) (shad RHI - shad RLO).
Definition INVS (mc : word -> option byte) : Prop :=
INV mc /\ rt_layout mc /\ unpoisoned mc Sa (Sa + NS) /\ wr_at asegs mc (shad RLO) (shad RHI - shad RLO)
/\ bytes_at asegs mc Sa (sstr ++ [Z_to_bv 8 0]) /\ rw_cells asegs mc (bv_unsigned a2) [C8 (Z_to_bv 64 Sa)].
Definition BND : Prop :=
(0 <= lo /\ lo <= bv_unsigned sp - 2320 /\ KHIGH <= lo /\ 1 <= NS /\ NS <= 2^40
/\ 0 < Sa /\ Sa + NS + 8 <= KEND
/\ 2147450880 <= shad RLO /\ shad RLO <= shad Sa /\ shad (Sa + NS - 1) + 1 <= shad RHI /\ shad RHI <= KHIGH
/\ 0 <= Z.shiftr Sa 3 < 2^44 /\ 0 <= Z.shiftr (Sa + NS + -1) 3 < 2^44
/\ shad RLO mod 8 = 0 /\ shad RHI mod 8 = 0
/\ RLO <= Sa /\ Sa + NS <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0
/\ bv_unsigned sp <= bv_unsigned a2 /\ bv_unsigned a2 + 8 <= 2^64)%Z.
#[using="m fstr ST LO KLO SEPV APPS SPOS NSZ R1"] Lemma BND_ok : BND.
Proof.
unfold BND. destruct ST as (L0 & _). destruct APPS as [LES AS]. unfold KLOW, KHIGH, KEND in *.
Local Ltac2 Set LiaHints.tbl := fun () => "0010>29784313979.76000001S".
rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF.
Z.div_mod_to_equations. nia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Ltac acc_facts B ::= pose proof BND_ok as B; unfold BND, KHIGH, KEND in B.
Definition BLS : Prop :=
(1 <= NS /\ NS <= 2^40 /\ 0 < Sa /\ Sa + NS + 8 <= 2^47
/\ 0 <= Z.shiftr Sa 3 < 2^44 /\ 0 <= Z.shiftr (Sa + NS + -1) 3 < 2^44
/\ 2147450880 <= shad RLO /\ shad RLO <= shad Sa /\ shad (Sa + NS - 1) + 1 <= shad RHI /\ shad RHI <= 17594333495296
/\ bv_unsigned sp <= bv_unsigned a2 /\ bv_unsigned a2 + 8 <= 2^64)%Z.
#[using="m lo fstr ST LO KLO SEPV APPS SPOS NSZ R1"] Lemma BLS_ok : BLS. Proof. pose proof BND_ok as B. unfold BND, KHIGH, KEND in B. unfold BLS. Local Ltac2 Set LiaHints.tbl := fun () => "0010>46427144719.7400000AS4SEPV4SPOS3NSZ1B".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="fstr ST LO KLO LAY VAQ SEPV SSTR SEPS APPS SPOS USTR NSZ R1 WR1"] Lemma invs_of : forall mc, INV mc -> INVS mc.
Proof.
intros mc IV. pose proof IV as (FRT & (j0 & FRL) & STM & ST1 & MU1 & WM1 & MI1 & GOT1 & SHB1).
pose proof BND_ok as B. unfold BND, KHIGH, KEND in B.
split; [exact IV|].
split. { eapply rw_cells_transport; [exact LAY | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. Local Ltac2 Set LiaHints.tbl := fun () => "0040?11805731844.87 22714190620.12135888805739.86 49752148685.87 00000;00C00I00OS2R11B4SEPVS1B1H2H0S2R11BS4SEPS".
lia. }
assert (SS : (shad (Sa + NS - 1) + 1 <= 17594333495296)%Z) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
split. { eapply unpoisoned_munch; [exact USTR | exact MU1 |]. cbn [disjoint_from]. lia. }
split. { eapply wr_at_transport; eassumption. }
split. { eapply bytes_at_transport; [exact SSTR | exact MU1 |]. rewrite length_app. cbn [length disjoint_from]. lia. }
eapply rw_cells_transport; [exact VAQ | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Ltac preps IV :=
let IVS := fresh "IVS" in pose proof (invs_of _ IV) as IVS;
destruct IVS as (_ & LAY1 & US1 & WR11 & SSTR1 & VAQ1);
prep IV;
let B := fresh "BS" in pose proof BLS_ok as B; unfold BLS in B;
change (?P) with (sf_hide P) in SEPS; change (?P) with (sf_hide P) in R1; change (?P) with (sf_hide P) in SEPV;
change (?P) with (sf_hide P) in SSTR; change (?P) with (sf_hide P) in NSZ.
Ltac unland K :=
change 18446744073709551615%Z with (Z.ones 64) in K; rewrite ?Z.land_ones in K by lia;
change (2 ^ 64)%Z with 18446744073709551616%Z in K.
Definition KS (Q : machine_state -> Prop) (i : Z) : Prop :=
forall mc' dcs', INV mc' -> rw_cells asegs mc' (bv_unsigned sp + -2216) dcs' -> cells_size dcs' = 40%nat ->
forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
evtF asegs RNG Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + i + 2)) (Z_to_bv 64 (bv_unsigned a2 + 8)) y22 y28 y29 y30 y31)
F (Z_to_bv 64 0x45348) fc None mc' (seg_rom asegs)).
Definition sregs (i : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31 : word) :=
mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp x5 x6 x7 sp (Z_to_bv 64 (-1)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 10) (Z_to_bv 64 (FMT + i + 2)) (Z_to_bv 64 0x152a7) (Z_to_bv 64 (bv_unsigned a2 + 8)) x22 x23
(Z_to_bv 64 (bv_unsigned sp + -2184)) (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) x28 x29 x30 x31.
#[using="fstr ST LO KLO FL FIMG RSTK sstr RLO RHI"] Lemma LS_X : forall Q i mc dcs, KS Q i -> INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcs -> cells_size dcs = 40%nat ->
forall x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31,
evtF asegs RNG Q (MS (sregs i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31)
F (Z_to_bv 64 0x456c8) fc None mc (seg_rom asegs)).
Proof.
intros Q i mc dcs K IV DIR SZ. intros. unfold sregs. Local Ltac2 Set LiaHints.tbl := fun () => "0010?50815571482.109000007S2LO2SZ".
prep IV.
zs. zs. unfold KS, lregs in K. eapply K; [| exact DIR | exact SZ].
split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="fstr ST LO KLO FL FIMG RSTK RLO RHI LAY VAQ SEPV SSTR SEPS APPS SPOS USTR NSZ R1 WR1 RSH1"] Lemma LS_L : forall Q i mc dcs (k : nat) (c : Z), KS Q i -> INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcs -> cells_size dcs = 40%nat ->
(NS <= 64)%Z -> Z.to_nat (shad (Sa + NS - 1) - c) = k -> (shad Sa <= c < shad (Sa + NS - 1))%Z ->
forall x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31,
evtF asegs RNG Q (MS (sregs i x1 x5 x6 x7 (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (Sa + NS + -1) 3)) (Z_to_bv 64 0) x13 x14 x15 x16 x17
(Z_to_bv 64 Sa) (Z_to_bv 64 NS) x28 x29 x30 x31)
F (Z_to_bv 64 0x457d8) fc None mc (seg_rom asegs)).
Proof.
intros Q i mc dcs k c K IV DIR SZ N1 Hk Hc. intros. unfold sregs. pose proof IV as IV0. Local Ltac2 Set LiaHints.tbl := fun () => "00;0?13714642969.12120713172464.13224122881917.1213268999899.147 50815571482.11559308585478.11659308627018.1  60890567713.12161136601015.12163282734874.11964505346068.13200000:00;00E00U00_00i00m01=01M01W01dS2SZ2Hk2HcFS2SZ2BS2HkS2SZ2Hk2Hc2H42H5S2LO2SZ2HkS2SZ2Hk2HcS2K'S2SZ2BS2Hk2Hc2SLS2SZ2Hk2Hc2SL2K1S2SZ2Hk2HcS2SZ2BS2Hk2Hc".
preps IV.
revert c x13 Hk Hc. induction k as [|k IH]; intros c x13 Hk Hc; [exfalso; lia|].
assert (SL : (shad (Sa + NS - 1) = 2147450880 + Z.shiftr (Sa + NS + -1) 3)%Z) by (unfold shad, ASHOFF; f_equal; f_equal; lia).
pose proof (unpoisoned_full_rd asegs mc Sa (Sa + NS) c US1 ltac:(lia)
ltac:(rewrite !shad_div in Hc; unfold ASHOFF in *; Z.div_mod_to_equations; lia)) as RDc.
zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K1; zify_cond K1.
- apply IH; lia.
- zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
eapply LS_X; eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="fstr ST LO KLO FL FIMG RSTK RLO RHI LAY VAQ SEPV SSTR SEPS APPS SPOS USTR NSZ R1 WR1 RSH1"] Lemma LS_E : forall Q i mc dcs, KS Q i -> INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcs -> cells_size dcs = 40%nat ->
(NS <= 64)%Z ->
forall x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31,
evtF asegs RNG Q (MS (sregs i x1 x5 x6 x7 (Z_to_bv 64 (2147450880 + Z.shiftr Sa 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (Sa + NS + -1) 3))
(Z_to_bv 64 (Sa + NS + -1)) x13 x14 x15 x16 x17 (Z_to_bv 64 Sa) (Z_to_bv 64 NS) x28 x29 x30 x31)
F (Z_to_bv 64 0x457bc) fc None mc (seg_rom asegs)).
Proof.
intros Q i mc dcs K IV DIR SZ N1. intros. unfold sregs. pose proof IV as IV0. Local Ltac2 Set LiaHints.tbl := fun () => "00C0?15389206808.13419033648638.13819480028200.12919480028203.13020288041906.11324122881528.11824993334705.13028034943372.18628442431488.13829784302302.13029784416728.11843608201231.11346022211189.15350815571482.11152074235542.12952525112625.13053508216722.12959308629082.1  7265205137.113 00000700>00I00T00X00_00c01@01H01L01P01T01h01o02602:02>02B02IS2SZ2H0S2SZ2H0S2SZ2BS3CK2S2SZ2BS3CK2S2SZS2SZ2BSS2SZS2SZ2B01H2H02H42H52H93H103H34S2SZ3CK2S2SZS2SZS2SZS2SZ2K62H42H52H93H10S2LO2SZS2SZ2BSS2SZS2SZS2K7S2SZ2BS".
preps IV.
destruct (unpoisoned_check_rd asegs mc Sa (Sa + NS) (Sa + NS + -1) 1 US1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b2 & RD2 & CK2).
unfold shad, ASHOFF in RD2. pose proof (sval_range b2) as SR2.
zstep. rewrite sxb_sval. do 5 zstep.
rewrite land7_mod. rewrite (aip_zero ((Sa + NS + -1) mod 8) (sval b2)) by (Z.div_mod_to_equations; lia).
zstep. if_cases K6; zify_cond K6.
- zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
eapply LS_X; eassumption.
- eapply (LS_L Q i mc dcs); [exact K | exact IV0 | exact DIR | exact SZ | exact N1 | reflexivity |].
unfold shad, ASHOFF in K6 |- *. rewrite !Z.shiftr_div_pow2 in K6 |- * by lia. change (2^3)%Z with 8%Z in K6 |- *.
Z.div_mod_to_equations; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="fstr ST LO KLO FL FIMG RI RSTK RLO RHI LAY VAQ SEPV SSTR SEPS APPS SPOS USTR NSZ R1 WR1 RSH1"] Lemma LS_C : forall Q i mc dcs, KS Q i -> INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcs -> cells_size dcs = 40%nat ->
forall x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
evtF asegs RNG Q (MS (sregs i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 Sa) (Z_to_bv 64 NS) x28 x29 x30 x31)
F (Z_to_bv 64 0x4576c) fc None mc (seg_rom asegs)).
Proof.
intros Q i mc dcs K IV DIR SZ. intros. unfold sregs. pose proof IV as IV0. Local Ltac2 Set LiaHints.tbl := fun () => "00e0?11447730086.17611667090694.12013478728930.12016232768748.12218185049160.12018185344072.11819575182546.12919626329698.12219628483873.11619628484135.11924115025142.12824117122301.13124122799997.11824936995894.12824936995895.12424944954523.11524945081531.11924947154174.12226552522358.11926552522358.12129549104648.15 29784302302.13430010325480.11830985198132.11731182322486.1233210808038.134 35438674554.11835497698988.11738885998408.12238959952907.12038960247819.1183970434365.122 40131048914.12942148837058.11943510366529.11645029014839.12045029506359.11846300107345.21146300107740.20450815571482.11352074235540.13256172410654.11957880736640.13458222164632.11959308628304.8  59308628566.8  59308628695.1  6164997574.150 62472604513.12062473096033.11862550303126.13765317419334.15 65744452519.12200000100800B00C00J00Q00U00\00c00j01101801?01K01W01c02202A02H02O02[02_02c02d02l02m03703;03<03C03J03Q03U03[03g03n04504^05G05N05U05Y05Z05a05h05o06306406;06B06F06O06PFS2SZ2BSS2R12SZ2BSFS2R12SZS2R12SZS2SZS2SZ2BSS2SZ2BSS2SZ2BSS2SZ2BSS2SZ2BSS2SZ2BSS4SPOS2SZ2BSS4SPOS2SZ2BSS4SPOS2SZ2BSS4SPOS2SZ2BS2N1S4SPOS2SZ2BS2N1S2SZ2BSS2SZ2BSS2BS2K21H2H0S2SZS2SZFS2SZ1B1HFS2R12SZ2BSS2SZFS2R12SZS2R12SZS2SZ2BSS2SZS2SZ1BS4SPOS2SZ2BSS2R12SZS2R12SZS2SZ2B01H2H02H42H52H93H103H143H153H243H39S2SZ2B01H2H02H42H52H93H103H143H153H193H34S2LO2SZS2SZ2BSS2SZFS2LO2SZS2BS2K1S2BS2K3S2K4FS2R12SZS2R12SZS2SZS2K21H2H0F".
preps IV.
zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1 BS. lia. }
zstep. zstep. zstep. if_cases K2; zify_cond K2.
-
assert (N1 : (64 < NS)%Z) by (unland K2; clear - K2 BS; Z.div_mod_to_equations; lia).
zstep. if_cases K3; zify_cond K3. 2:{ exfalso. clear -K3 BS. lia. }
zstep. zstep. zstep.
unfold sf_hide in LO.
call_sp rip_spec;
[ exact MI1 | exact ST1 | lia | unfold KHIGH; lia | exact GOT1 | exact SHB1 | exact LAY1
| zsimp; exact APPS | zsimp; exact US1
| zsimp; pose proof BND_ok as B9; unfold BND in B9; lia
| eapply rng_sub'; [exact RSTK | lia] | ].
zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
eapply LS_X; [exact K | | eassumption | exact SZ].
split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
-
assert (N1 : (NS <= 64)%Z) by (unland K2; clear - K2 BS; Z.div_mod_to_equations; lia).
do 11 zstep.
change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia. zsimp.
unfold sf_hide in R1.
destruct (shadow_probe8 asegs mc RLO RHI Sa WR11 ltac:(apply no_image_asan; pose proof BND_ok as B9; unfold BND in B9; lia)
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w1 P1].
destruct (shadow_probe8 asegs mc RLO RHI (Sa + NS + -1) WR11 ltac:(apply no_image_asan; pose proof BND_ok as B9; unfold BND in B9; lia)
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold KEND in R1; lia)) as [w2 P2].
unfold ASHOFF in P1, P2.
do 4 zstep. prr [10;11;12;13]%Z. if_cases K5; zify_cond K5.
+ eapply LS_X; eassumption.
+ eapply LS_E; eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="ST LO KLO FL FIMG RI RSTK Sa sstr RLO RHI LAY VAQ SEPV SSTR SNOZ SEPS APPS SPOS USTR NSZ R1 WR1 RVA RS RSH1"] Lemma L_dirS : forall Q mc (i : Z) bc,
INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) (dcellsA (FMT + i) bc) ->
(0 <= i)%Z -> (i + 2 <= L)%Z -> sconv (bv_unsigned bc) -> KS Q i ->
forall y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
evtF asegs RNG Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp (Z_to_bv 64 (FMT + i)) (Z_to_bv 64 (bv_unsigned bc)) y11 y12 y13 y14 y15 y16 y17
(Z_to_bv 64 10) (Z_to_bv 64 (FMT + i + 2)) (Z_to_bv 64 0x152a7) a2 (Z_to_bv 64 (FMT + i + 1)) (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned sp + -2184))
(Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31)
F (Z_to_bv 64 0x454f8) fc None mc (seg_rom asegs)).
Proof.
intros Q mc i bc IV DIR Hi HiL HC K. intros. pose proof IV as IV0. Local Ltac2 Set LiaHints.tbl := fun () => "00g0?11609845426.13611611941819.13312470816612.12715798567580.13217720687452.15117948135870.1281810977457.127 19484756833.15020828558108.13423117826083.13024800094436.13124945081918.13724947425214.13629239924756.12729239925651.13029239926046.13329240271650.12429685547187.14629717215544.13529717215547.13729719312689.14729719312689.1503281570046.134 33115000180.13134591193778.13634886800810.13335220170288.13839367131707.13340384252295.12440384344753.12740733335832.14444291154750.13745373595996.13645373595996.13845373595996.14845373595996.15147027545905.12747654475482.14750346513340.14550815571482.11450874424251.13350874424630.13057017640331.13657019736194.13357020178110.12459308628179.3  59308628179.8  61330630062.13365247782060.13265247782060.14865508693430.13065562238940.1327826451026.124 8131073892.131 8131073896.147 00000100200300400500600700800900:00;00G00S00W00[00_00c00d00e00f00g00h00i00j00k00l00m00n00o01001101201301401501601701801901=01>01?01@01A01B01I01P01Q01R01S01T01U01V01W01XSSSSSSSSSSSS4SPOS2R12BSS4SPOS2R12BSS2CRS2CRS2CRS2CRSSSSSSSSSSSSSSSSSSSSSSS2LOSSSSSS2K02CCS2BS2K0SSSSSSSS".
preps IV.
destruct (sfacts _ HC) as (_ & CR & N109 & N110 & F3 & F4 & F5 & F6).
pose proof (conj CR (conj N109 N110)) as CC.
recell DIR 2%nat 1%nat [C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 4294967295)].
zs. change (sx32 (Z_to_bv 64 4294967295)) with (Z_to_bv 64 (-1)). zs. br CC.
zs. change (sx32 (Z_to_bv 64 4294967295)) with (Z_to_bv 64 (-1)). zs. br CC.
zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
zs. cbv beta. zs. zs. br CC. zs. zs. zs.
call istrchr_spec. all: prem. unfold istrchr_res. rewrite F3. rewrite unsigned_lit by (cbn; lia).
zs. cbv beta. zs. br CC.
zs. zs. zs. zs. call istrchr_spec. all: prem. rewrite (istrchr_res_none _ _ _ F4).
zs. zs. zs. br CC.
zs. zs. zs. zs. call istrchr_spec. all: prem. unfold istrchr_res. rewrite F5. rewrite unsigned_lit by (cbn; lia).
zs. zs. br CC. zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
zs. zs.
zs. cbv beta. zs. zs. zs. call istrchr_spec. all: prem. unfold istrchr_res. rewrite F6. rewrite unsigned_lit by (cbn; lia).
zs. br CC. zs.
zs. cbv beta. zs. zs. br CC.
zs. zs. br CC. zs. br CC.
zs. zs. zs. br BS.
zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
zs. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0). zs. br CC.
zs. zs.
unfold sf_hide in SSTR1.
call istrlen_spec. all: prem.
zs.
cbn [app] in DIR.
eapply (LS_C Q i); [exact K | | exact DIR | reflexivity].
split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="FMT MI ST LO KLO GOT SHB A1 FB NOZ FL FIMG FZ RI RSTK RSHF Sa sstr RLO RHI LAY VAQ SEPV SSTR SNOZ SEPS APPS SPOS USTR NSZ R1 WR1 RVA RS RSH1"] Theorem printf_common_str1 : forall pre b37 bc post,
fstr = pre ++ b37 :: bc :: post ->
Forall (fun b : byte => bv_unsigned b <> 37%Z) pre -> Forall (fun b : byte => bv_unsigned b <> 37%Z) post ->
bv_unsigned b37 = 37%Z -> sconv (bv_unsigned bc) -> post <> [] ->
evtF asegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x4523c) fc None m (seg_rom asegs)).
Proof.
intros pre b37 bc post EF NP1 NP2 E37 HC NE.
Local Ltac2 Set LiaHints.tbl := fun () => "00Y0?14105795920.19315047277527.12720710540893.20520719526996.20723552344883.18024314867220.19626265415335.14327654620486.12527752260210.14327994577949.18028532548836.18029227258478.15829227258595.14329539222706.12733555826544.1433405560941.158 3405561056.143 37393454705.14338021105375.85 39203413114.21040599393995.2064115694607.143 41610801092.20645530951034.22448836336870.83 5035459121.205 5044183096.207 50815571482.19251077630375.21056221793875.20756230894682.20557667503202.20757676621419.20559308661201.17959314923118.3  59702536596.13160536134864.20560544204505.20760584206281.20560592143808.2079496291333.205 00000F00O00P00Q00]00i01:01C01O01^01m02>02O02[02d03503F03O03T03j04804I04W04j04k04l04m05<05M05N05O05P05Q05`05g06;06<06=06>06?06PS4SPOS2R13LEN3NE'2SZ1BS3LEN3NE'FFS3LEN3NE'2SZS3LEN3NE'2SZS4SPOS2R13LEN3NE'S3LEN3NE'S2R13LEN3NE'S2R13LEN3NE'2SZS2R13LEN3NE'2SZS4SPOS2R13LEN3NE'S4SPOS2R13LEN3NE'S2R13LEN3NE'S3LEN3NE'S4SPOS2R13LEN3NE'S4SPOS2R13LEN3NE'S3LEN3NE'S3LENS4SPOS2R13LEN3NE'1B2HjS2R13LEN3NE'1BS4SPOS2R13LEN3NE'S2R13LEN3NE'1BS4SPOS2R13LEN3NE'1BSFFS2LO3LEN3NE'2SZS2R13LEN3NE'1B2HjFFFFS3LEN3NE'2SZ2E2S3NZ21KS4SPOS2R13LEN3NE'2HjFFFFS2R13LEN3NE'2SZ1B".
assert (LEN : length fstr = (length pre + 2 + length post)%nat) by (rewrite EF, length_app; cbn; lia).
assert (NE' : (1 <= length post)%nat) by (destruct post; [congruence | cbn; lia]).
set (np := Z.of_nat (length pre)).
eapply L_entry. intros mc dj IV DIR. intros.
eapply (L_head _ mc [CB 40 dj]); [exact IV | exact DIR | reflexivity |]. clear mc dj IV DIR. intros mc IV DIR. intros.
replace (Z_to_bv 64 FMT) with (Z_to_bv 64 (FMT + 0)) by (f_equal; lia).
pose proof IV as IV'. destruct IV' as (_ & _ & _ & _ & MUc & _ & MIc & _).
eapply (L_skip _ mc (length pre) 0); [exact MIc | exact MUc | lia | lia | |].
{ intros j b Hj Hb. eapply (proj1 (Forall_forall _ _) NP1). eapply nth_error_In. rewrite EF, nth_error_app1 in Hb by lia. exact Hb. }
clear MUc MIc. intros. rewrite Z.add_0_l.
eapply (L_dirA _ mc np _ b37 bc); [exact IV | exact DIR | lia | lia | | exact E37 | | exact (proj1 (sfacts _ HC)) |].
{ rewrite EF. replace (Z.to_nat np) with (length pre) by lia. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. }
{ rewrite EF. replace (Z.to_nat (np + 1)) with (length pre + 1)%nat by lia. rewrite nth_error_app2 by lia.
replace (length pre + 1 - length pre)%nat with 1%nat by lia. reflexivity. }
clear mc IV DIR. intros mc IV DIR. intros.
eapply (L_dirS _ mc np); [exact IV | exact DIR | lia | lia | exact HC |].
clear mc IV DIR. unfold KS. intros mc dcs IV DIR SZ. intros. unfold lregs.
destruct (nth_error post 0) as [b2|] eqn:E2. 2:{ exfalso. apply nth_error_None in E2. lia. }
assert (H2 : nth_error fstr (Z.to_nat (np + 2)) = Some b2).
{ rewrite EF. replace (Z.to_nat (np + 2)) with (length pre + 2)%nat by lia. rewrite nth_error_app2 by lia.
replace (length pre + 2 - length pre)%nat with 2%nat by lia. exact E2. }
pose proof IV as IV'. prep IV'.
destruct (fmt_char mc (np + 2) MI1 MU1 ltac:(lia)) as (b2' & Hb2 & NZ2 & RB2 & RD2). rewrite H2 in Hb2. injection Hb2 as <-.
replace (FMT + np + 2)%Z with (FMT + (np + 2))%Z by lia.
zs. cbv beta. zs. assert (CC : True) by exact I. br NZ2.
eapply (L_head _ mc dcs); [exact IV | exact DIR | exact SZ |].
clear mc IV DIR SZ FRT FRL STM ST1 MU1 WM1 MI1 GOT1 SHB1 RD2. intros mc IV DIR. intros.
pose proof IV as IV'. destruct IV' as (_ & _ & _ & _ & MUc & _ & MIc & _).
eapply (L_skip _ mc (length post) (np + 2)); [exact MIc | exact MUc | lia | lia | |].
{ intros j b Hj Hb. eapply (proj1 (Forall_forall _ _) NP2). eapply nth_error_In with (n := (j - (length pre + 2))%nat).
rewrite EF, nth_error_app2 in Hb by lia.
replace (j - length pre)%nat with (S (S (j - (length pre + 2)))) in Hb by lia. exact Hb. }
intros. replace (np + 2 + Z.of_nat (length post))%Z with L by lia.
eapply L_last; [exact IV | exact DIR].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End PC.
End CANSEC1.
