(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import MM_syscalls.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import SysStepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg AProto ABase AKit AKit2 RT_stubs.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
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

Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
Definition rmap_entry := 0x6ea5c.
End CANSEC1.
Notation RMAP_STACK := 400 (only parsing).
Notation RMAPD_STACK := 368 (only parsing).
Section CANSEC2. Context {rc : runConstT}.
Definition rmap_cells (m : amem) : Prop :=
rw_cells asegs m 0x99760 [C8 (Z_to_bv 64 0x131f20)]
/\ rw_cells asegs m 0x131f20 [C8 (Z_to_bv 64 4096)]
/\ rw_cells asegs m 0x99770 [C8 (Z_to_bv 64 0x133fa8); C8 (Z_to_bv 64 0x9fc78); C8 (Z_to_bv 64 0xa2478);
C8 (Z_to_bv 64 0xa3168); C8 (Z_to_bv 64 0xa3170); C8 (Z_to_bv 64 0xa3160)]
/\ rw_cells asegs m 0x1340ac [C1 (Z_to_bv 8 0)]
/\ rw_cells asegs m 0x134038 [C8 (Z_to_bv 64 0)].
Definition rmap_postD (D : Z) (RNG : footprint) (sp : word) (addr size lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
fp_le RNG RNG'
/\ addr + size <= ATOP
/\ munch [(bv_unsigned sp - D, bv_unsigned sp); (addr, addr + size)]%Z m m' /\ wmono asegs m m'
/\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' addr [CB (Z.to_nat size) (repeat (Z_to_bv 8 0) (Z.to_nat size))]
/\ rng RNG' addr size /\ rng RNG' (shad addr) (shlen size)
/\ fp_bw RNG'
/\ rmap_cells m'.
Definition rmap_post := rmap_postD RMAP_STACK.
#[using="Type"] Lemma page_round_up_mult : forall s, s mod 4096 = 0 -> 0 <= s -> page_round_up_Z s = s.
Proof. intros s Hs H0. unfold page_round_up_Z, page_size. Z.div_mod_to_equations. nia. Qed.
#[using="Type"] Lemma land_align4096 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709547520 = x - x mod 4096.
Proof.
intros x Hx.
replace 18446744073709547520 with (Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity.
replace (x - x mod 4096) with (Z.shiftl (Z.shiftr x 12) 12).
2:{ Local Ltac2 Set LiaHints.tbl := fun () => "0080>10351595562.5 17210504373.5 17210506534.3 19456077695.7 35497642613.5 56093574452.7 67041143748.109074610895.7  00000400500600900:00A00D00HS2HiSSS1LSS2Hx2NZS1HS2Hx".
rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^12) with 4096. Z.div_mod_to_equations. lia. }
rewrite <- Z.ldiff_ones_r by lia.
apply Z.bits_inj'. intros i Hi.
rewrite Z.land_spec, !Z.ldiff_spec, !Z.testbit_ones_nonneg by lia.
destruct (Z.ltb_spec i 64) as [L|L]; cbn.
- reflexivity.
- destruct (Z.eq_dec x 0) as [->|NZ]. { rewrite Z.bits_0. reflexivity. }
rewrite (Z.bits_above_log2 x i); [reflexivity| lia |].
apply Z.lt_le_trans with 64; [|lia]. apply Z.log2_lt_pow2; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma land_align2p18 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709289472 = x - x mod 262144.
Proof.
intros x Hx.
replace 18446744073709289472 with (Z.ldiff (Z.ones 64) (Z.ones 18)) by reflexivity.
replace (x - x mod 262144) with (Z.shiftl (Z.shiftr x 18) 18).
2:{ Local Ltac2 Set LiaHints.tbl := fun () => "0080>10351595562.5 19456077695.7 19939214485.5 19939216646.3 35497642613.5 56093574452.7 67041143748.109074610895.7  00000400700800900:00A00D00HS2HiS1LSSSS2Hx2NZS1HS2Hx".
rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^18) with 262144. Z.div_mod_to_equations. lia. }
rewrite <- Z.ldiff_ones_r by lia.
apply Z.bits_inj'. intros i Hi.
rewrite Z.land_spec, !Z.ldiff_spec, !Z.testbit_ones_nonneg by lia.
destruct (Z.ltb_spec i 64) as [L|L]; cbn.
- reflexivity.
- destruct (Z.eq_dec x 0) as [->|NZ]. { rewrite Z.bits_0. reflexivity. }
rewrite (Z.bits_above_log2 x i); [reflexivity| lia |].
apply Z.lt_le_trans with 64; [|lia]. apply Z.log2_lt_pow2; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma adec_mmap_rw_Some : forall len rsp a, adec_mmap ATOP len 3 rsp = Some a ->
exists ci, rsp = mkEffectU (Z_to_bv 64 a) [] [(wa a, Z_to_bv 64 (mmap_len len))] [] [] ci
/\ a mod 4096 = 0 /\ 0 < a /\ a + mmap_len len <= ATOP.
Proof.
intros len rsp a H. unfold adec_mmap in H. cbn [Z.eqb] in H.
destruct (dec_mmap ATOP len [] rsp) as [[e|a']|] eqn:D; try discriminate. injection H as <-.
destruct (dec_mmap_Some _ _ _ _ _ D) as [ci [E OK]]. exists ci. split; [exact E|].
pose proof (mmap_addr_ok_true _ _ _ _ OK) as [(M1 & M2 & M3) _]. unfold page_size in M1. auto.
Qed.
#[using="Type"] Lemma rmap_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (addr size lo : Z),
stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RMAP_STACK ->
mem_inv asegs m ->
a1 = Z_to_bv 64 addr -> a2 = Z_to_bv 64 size -> 0x10000 <= bv_unsigned a3 < 2^47 ->
addr mod 4096 = 0 -> size mod 4096 = 0 -> 0 < size -> AIMG_HI <= addr -> addr + size < 2^63 ->
rmap_cells m ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
(forall a RNG' ms', a <> addr -> 0 < a -> a + size <= ATOP -> implS asegs RNG' (K a) (epostF Q) ms') ->
(forall RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
rmap_post RNG sp addr size lo m RNG' m' ->
implS asegs RNG' (K addr) (epostF Q)
(MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
implS asegs RNG (ebind (enode (NMmap addr size 3 50) (adec_mmap ATOP size 3)) K) (epostF Q)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmap_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros ST CEIL LO MI -> -> NAME AAL SAL SPOS A0 ASZ RC RIMG RSTK UNR KONT. unfold AIMG_HI in A0.
pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & GOT & DPM & MLIM).
unfold rmap_entry in *. word_range sp SPR. word_range a3 A3R.
pose proof (munch_refl [(bv_unsigned sp - RMAP_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
eapply (implF_ebind _ _ _ _ _ _ _
(fun a RNG' ms' => (a <> addr /\ 0 < a /\ a + size <= ATOP) \/ a = addr /\ exists m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
rmap_post RNG sp addr size lo m RNG' m' /\
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))).
2: { intros a RNG' ms' [(NE & P1 & P2)|[-> PO]]; [apply UNR; [exact NE | exact P1 | exact P2]|].
destruct PO as (m' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & PO & ->).
eapply KONT. exact PO. }
iprefix.
Local Ltac2 Set LiaHints.tbl := fun () => "04g0?10439767981.76 10439767981.77 10667180602.80 10835893820.80 11490489838.77 1162083374.77  1164180522.100 11805467289.72 11805467289.73 11805467289.74 11805467289.75 11805467289.76 11805467289.77 11805467289.78 11805467289.79 11805467289.80 11833462140.99 11903774446.72 12017784537.99 12844062062.78 12866317849.78 13084834179.78 13084834179.81 13169897334.99 13186349962.86 13219133678.72 13725786656.82 13725786670.79 14782759150.72 14869079534.75 15062336688.76 1543849006.99  15685060272.73 16295403374.78 16395817388.86 16473946862.80 16640242030.78 16643491566.75 16781328285.76 16844590268.77 17221588796.72 17292611950.76 17657838574.80 17776320429.72 17778417576.98 17976286208.2  18104477166.80 18105812974.77 1863552366.78  18689773242.77 18848698606.78 19006120615.75 19376804346.99 19491992743.75 19506020846.77 2003044974.76  20289765031.77 20633589486.78 2099171026.73  2099171026.76  21456922734.76 21931701891.80 21931701891.83 22080489625.78 22163107130.78 22206135662.78 22439364775.76 22591915566.99 22872305980.80 23230285244.74 23909860377.78 24080369177.78 24179267756.77 24179267758.80 24365389228.86 24487705898.73 24630998586.78 2478755310.80  25029166211.10125029166211.78 25071629079.99 25117511228.78 25255714158.78 25435258127.73 25435258127.99 25566553219.75 25566553219.99 25876173099.99 25878270254.77 26000888601.77 26115614154.99 26278908583.76 26346213514.84 26494020268.86 26868428163.76 26868428163.98 27066288442.77 27624344046.78 27679091076.67 2772514414.80  27730847314.73 27730847314.76 27911502958.76 28636712686.79 28830049838.99 28859544046.74 28885198780.78 29212037676.20 29515017603.77 29515017603.78 29693776878.77 30196181434.76 30231011258.78 30518562691.10030518562691.76 30890730486.99 31143001276.76 31193132057.78 31287922286.76 31420974624.72 31929422315.78 31940628442.70 32099668718.80 32103103726.78 32431485806.76 32651489978.76 32905389884.77 33342412455.78 33473183726.80 33680001082.72 34288016811.98 34290115814.66 35082589626.78 35153358318.78 3520940321.81  3520940335.78  35677373209.76 36107562391.89 36115622435.97 36115622445.74 36148814574.79 36367760551.78 37044431129.77 37153923388.75 37729779438.78 37844949358.76 3787933806.76  38687199342.76 38806986883.72 38806986883.98 3888239342.72  38916199868.78 39055981550.77 39129884846.99 39939624357.86 40091925667.97 40091925676.75 40259044249.79 40987550979.99 41564619544.85 4240063612.85  42501437472.10042501437472.99 42503534630.75 42505299482.70 42509314849.83 42511603879.86 42511604512.86 42511604641.85 42744733806.74 42817538363.86 42831019478.73 42831019478.76 43059266230.64 43183609788.76 43231650947.80 43231650947.83 43466089753.76 43985854248.98 43987951407.74 44158664835.75 44158664835.98 44621604505.77 446960878.75   45221239098.75 46232973498.76 46556098215.78 46657085550.75 47196384886.99 47215438702.72 47291567726.77 47373904281.79 48355031171.77 48355031171.80 48945323886.78 49978085870.75 50215255347.76 50346867566.78 50357606254.79 50362574674.73 50362574674.76 50647975150.78 50862133932.77 50862133934.80 50882889347.79 50882889347.82 51678667180.75 51680764331.99 5180980284.75  51840259694.76 51933874855.78 53324805799.79 53618414247.80 53767577772.73 53769674920.98 54148288295.99 54160885230.76 54352578414.78 54618151079.74 54688491502.78 55104759171.74 55104759171.99 55188037614.78 55442533998.76 55467843644.79 55530626798.78 55681940633.77 5575378989.76  5575378991.79  55837769369.80 56050883492.13 563227834.74   56702368758.81 56759370246.7  56993697826.86 5745572519.80  57496811886.80 57756175257.80 58655119491.10058655119491.78 58762852128.82 58762852142.79 59012487214.99 59044679705.76 59178106163.73 59308628179.3  59308628566.3  59314873579.7  59314873579.8  59410257006.78 59608349294.77 59805822339.78 59805822339.81 59970707310.75 60077573358.79 60357415926.98 60468873383.76 60499277734.69 60634079619.10060634079619.76 61230833468.78 6165337146.79  6166287527.72  61917199020.75 61919296171.99 62131122447.76 62131122447.82 62625805991.77 62923854958.77 62948418713.80 62989950816.81 62989950828.75 63235321891.97 63235321901.71 63341493050.80 64135124206.80 6501784985.78  65088762478.74 65104334021.84 65104452412.5  65759081031.69 65805175866.75 65806924526.75 65977411438.76 66656729710.74 66680029612.86 66747928658.73 66747928658.76 6676984046.80  67258535356.76 67434480419.86 67449453465.75 67471419575.85 67943285742.75 68156076782.76 68309604434.73 68309604434.76 68343577710.77 68685913326.75 6897720302.76  802261998.75   8390799470.77  8405736896.100 8405736896.99  8474926972.71  8684881006.74  8733664836.71  9055284462.79  9492323756.86  97018265.80    9767205155.86  00000400800=00A00J00N00R00S00T00U00V00W00X00Y00Z00[00_00h00i01201301401501601701@01D01H01Q01Z01^01g01k02402802A02J02S02T02X02\02e02n03203603<03E03N03W03\03e03f03k03l04504>04?04H04Q04Z04c04d04e04f04k05405505>05B05F05G05H05L05P05T05U05Z05c05d05e05f05j06306406506606706;06?06@06R06S06T06X06Y06Z06_06h06l07507>07G07P07Y07b07k07o08<08=08>08G08L08Q08R08S08T08X08Y08b08f09309@09I09R09[09`09d09e09n0:30:70:80:=0:F0:J0:N0:O0:U0:Y0:]0:f0:g0:h0:l0;50;>0;G0;P0;Q0;R0;[0;_0;h0<10<50<90<=0<>0<?0<@0<A0<H0<O0<\0<i0=60==0=D0=Q0=Z0=[0=`0=e0=i0=m0=n0=o0>00>40>80>90>:0>;0>D0>I0>N0>O0>X0>Y0>b0>k0>l0>m0>n0?70?@0?A0?J0?S0?\0?e0?n0@20@60@70@80@<0@@0@D0@M0@N0@O0@P0@T0@X0@Y0@b0@k0@l0A50A60A70A@0AI0AM0AV0AW0A[0A_0A`0Ae0Aj0Ak0B;0B?0B@0BI0BJ0BK0BL0BP0BT0B]0B^0B_0Bh0Bo0C>0CP0CY0Cb0Cc0Cd0Cm0D60D70D80D<0D=0D>0DB0DG0DH0DL0DP0DQ0DR0DS0D\0D]0Da0De0Di0Dm0E20E;0E<0EE0ER0E_0E`0Ee0En0F70F@0FD0FM0FV0F_0Fc0G00G10G60G?0GH0GQ0GZ0Gc0Gl0H50H>0HG0HH0HI0HJ0HS0HT0H]0Ha0Hb0HoS2LOS2LOS3SPRS2HBS4CEIL2LOS2LOS2LOSSSSSSSSSS2HBS4CEIL2LOSS4CEIL2LOSSSSSS4CEIL2LOS2LOS2LOS4CEIL2LOS4CEIL2LOS2HBS4CEIL2LOS2HBS4CEIL2LOS2A0S4CEIL2LOS4CEIL2LOS4CEIL2LOSS2HBS2HBS4CEIL2LOS4CEIL2LOS2LOS2LOS4SPOSS4CEIL2LOS4CEIL2LOS4CEIL2LOS3SPRS4CEIL2LOSS3SPRSS4CEIL2LOS4CEIL2LOSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSSSS3SPRS4CEIL2LOSS4CEIL2LOS2HBS2HBSSS2LOS2LOS2A0SS3SPRS4CEIL2LOSSSS2HBS4CEIL2LOSSSSS2LOS2LOSS4CEIL2LO4SPOS3AM3SSS2A0SSS3SPRS4CEIL2LOS2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS2HBS3SAL1H2H02H4SSS4CEIL2LOS3SPRS3SPRSSSS2HBSS4CEIL2LOS2LOS4SPOS2A03ASZS4SPOS2A03ASZS4CEIL2LOS4CEIL2LOS4CEIL2LOS3SPRS2HBSS4CEIL2LOS3SPRS2LOSS3SPRS4CEIL2LOS2LOS2LOSS2A01HS2LOS2LOS4CEIL2LOSSS2HBS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSSS4CEIL2LOS2HBS4CEIL2LOS4CEIL2LOS2LOS2LOS2LOSSSSS2A02K1S2A02K1S4SPOS2A03ASZS4SPOS2A03ASZS4SPOS2A03AM3S2A02K1S2A02K1S4SPOS2A03AM3S4CEIL2LOSS3SPRS3SPRS2LOS2HBSSSS2LOS2LOSSSS4CEIL2LOS3SPRS3SPRSS4CEIL2LOSS4CEIL2LOS4CEIL2LOSSSS4CEIL2LOS4CEIL2LOSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS2LOS2LOSSS2LOS2LOS2HBS4CEIL2LOSSSS2LOS2LOSS4CEIL2LOS4CEIL2LOSS4CEIL2LOSSS4CEIL2LOS4CEIL2LOS2HBS4CEIL2LOSS2LOS2LOSS3AALS3SPRSS4SPOS3AM23AM31HS2LOSS4CEIL2LOSSSS2LOS2LOS4CEIL2LOSSS4NAME2K0S2A02K3S4SPOS3AM32LT1HS4SPOS3AM32K11H2K2S4CEIL2LOS4CEIL2LOSSS4CEIL2LOS4CEIL2LOSSS2LOSSS2HBS3SPRSS2LOS2LOSSSS4CEIL2LOSS2LOS2LOS2LOS2LOS3SPRS4CEIL2LOSS4CEIL2LOS4SPOS2A03AM3S4SPOS2A03ASZSS3SPRS4CEIL2LOS4CEIL2LOS4CEIL2LOS2A0S4CEIL2LOS4CEIL2LOS4CEIL2LOS2HBS4CEIL2LO3AM3SS3ASZS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOFFSS4CEIL2LOSS4CEIL2LOS2A0SS4CEIL2LO3AM3".
carve_frame 32%nat ST.
step. step. step. step. step. step. step.
step. step. step. step.
step. step. step.
carve_frame 96%nat ST.
step. step. step. step. step. step. step.
step. step. step.
step. step. step.
step. step. if_lit.
zstep. zstep. step. if_lit.
zstep. zstep. zstep. zstep.
setreg 8 (Z_to_bv 64 size) ltac:(rewrite land_align4096 by lia; f_equal; clear -SAL SPOS ASZ A0; Z.div_mod_to_equations; lia).
step. if_lit.
zstep.
setreg 18 (Z_to_bv 64 addr) ltac:(rewrite land_align4096 by lia; f_equal; clear -AAL A0 ASZ SPOS; Z.div_mod_to_equations; lia).
step. step. step. step. step.
step.
carve_frame 272%nat ST.
step. step. step. step. step. step. step. step.
step. step.
step. if_cases K0; zify_cond K0. { exfalso. clear -K0 NAME. lia. }
step. step. step. lstep.
zstep. step. if_lit.
zstep.
step. step. step. step. step. step. step. step. step.
release_frame FR1 ST (bv_unsigned sp + -128).
step. setreg 13 (Z_to_bv 64 50) ltac:(vm_compute; reflexivity).
step. step. step. step. step.
step.
icallk rt_mmap_stubP.
intros a RNG' ms' (rsp & HF & Hdec & ->).
destruct (adec_mmap_rw_Some _ _ _ Hdec) as (ci & -> & AM1 & AM2 & AM3).
pose proof (page_round_up_mult size SAL ltac:(clear -SPOS; lia)) as PRU. unfold mmap_len in *. rewrite PRU in AM3. rewrite PRU.
pose proof (fstepS_mmap_grant addr size 50 _ RNG RNG' HF (eq_refl : Z.land 50 MAP_NORESERVE = 0)) as GR. cbn [eff_ret] in GR.
rewrite (unsigned_lit a) in GR by (clear -AM2 AM3 SPOS; lia). rewrite (unsigned_lit size) in GR by (clear -SPOS ASZ A0; lia).
rewrite PRU in GR. specialize (GR ltac:(unfold page_size; exact AM1)). destruct GR as [GR1 GR2].
pose proof HF as HF0. fstepS_transport HF.
destruct (Z.eq_dec a addr) as [->|NE]. 2: { apply evtF_done. left. split; [exact NE|]. split; [exact AM2| atop_facts; exact AM3]. }
unfold rt_regs. cbn [eff_ret]. rewrite eff_mem_zeros.
replace (ret_pc (Z_to_bv 64 420048)) with (Z_to_bv 64 420048 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
apply (munch_weaken _ [(bv_unsigned sp - RMAP_STACK, bv_unsigned sp); (addr, addr + size)]%Z) in MU.
2: { unfold sub_fp. cbn [outside]. clear. intros x Hx. tauto. }
sys_mem_zeros.
step. step. step.
step. step. step. if_cases K1; zify_cond K1. 2: { exfalso. clear -K1 AM3 SPOS A0. lia. }
zstep. step.
setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 addr) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
step. step. step. step. step. step.
step. step. step. if_cases K2; zify_cond K2. 2: { exfalso. clear -K2 AM3 SPOS A0. lia. }
zstep. step.
setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 addr) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
step. if_lit.
step. step.
step. step. step. step. if_lit. step.
step. step. step. step. step. step. step. step. step.
lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -128) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp + -32) end.
replace (ret_pc (Z_to_bv 64 453256)) with (Z_to_bv 64 453256 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by (clear -A0 ASZ SPOS; unfold AIMG_HI in *; lia). clear -K3 A0. lia. }
step. step. step. step. step. step.
lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -32) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
apply evtF_done. right. split; [reflexivity|].
do 15 eexists. split. 2: reflexivity.
unfold rmap_post, rmap_postD. destruct HF0 as [[FPLE _] [_ BW]].
split; [exact FPLE|]. split; [exact AM3|].
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
split; [exact ZNEW|]. split; [exact GR1|]. split; [exact GR2|]. split; [exact BW|].
unfold rmap_cells. repeat (split; [assumption|]). assumption.
Unshelve. all: apply ref_ro_addr_false; right; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC2.
