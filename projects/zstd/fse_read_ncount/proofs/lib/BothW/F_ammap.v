(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import MM_syscalls.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import SysStepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg AProto ABase AKit AKit2 RT_stubs.
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
Definition rmap_entry := 0x6e948.
End CANSEC1.
Notation RMAP_STACK := 400 (only parsing).
Notation RMAPD_STACK := 368 (only parsing).
Section CANSEC2. Context {rc : runConstT}.
Definition rmap_cells (m : amem) : Prop :=
rw_cells bsegs m 0x998f0 [C8 (Z_to_bv 64 0x131fe0)]
/\ rw_cells bsegs m 0x131fe0 [C8 (Z_to_bv 64 4096)]
/\ rw_cells bsegs m 0x99900 [C8 (Z_to_bv 64 0x134068); C8 (Z_to_bv 64 0x9fd38); C8 (Z_to_bv 64 0xa2538);
C8 (Z_to_bv 64 0xa3228); C8 (Z_to_bv 64 0xa3230); C8 (Z_to_bv 64 0xa3220)]
/\ rw_cells bsegs m 0x13416c [C1 (Z_to_bv 8 0)]
/\ rw_cells bsegs m 0x1340f8 [C8 (Z_to_bv 64 0)].
Definition rmap_postD (D : Z) (RNG : footprint) (sp : word) (addr size lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
fp_le RNG RNG'
/\ addr + size <= ATOP
/\ munch [(bv_unsigned sp - D, bv_unsigned sp); (addr, addr + size)]%Z m m' /\ wmono bsegs m m'
/\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp)
/\ rw_cells bsegs m' addr [CB (Z.to_nat size) (repeat (Z_to_bv 8 0) (Z.to_nat size))]
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
stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RMAP_STACK ->
mem_inv bsegs m ->
a1 = Z_to_bv 64 addr -> a2 = Z_to_bv 64 size -> 0x10000 <= bv_unsigned a3 < 2^47 ->
addr mod 4096 = 0 -> size mod 4096 = 0 -> 0 < size -> AIMG_HI <= addr -> addr + size < 2^63 ->
rmap_cells m ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
(forall a RNG' ms', a <> addr -> 0 < a -> a + size <= ATOP -> implS bsegs RNG' (K a) (epostF Q) ms') ->
(forall RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
rmap_post RNG sp addr size lo m RNG' m' ->
implS bsegs RNG' (K addr) (epostF Q)
(MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
implS bsegs RNG (ebind (enode (NMmap addr size 3 50) (adec_mmap ATOP size 3)) K) (epostF Q)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmap_entry) fc None m (seg_rom bsegs)).
Proof.
intros until lo. intros ST CEIL LO MI -> -> NAME AAL SAL SPOS A0 ASZ RC RIMG RSTK UNR KONT. unfold AIMG_HI in A0.
pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & GOT & DPM & MLIM).
unfold rmap_entry in *. word_range sp SPR. word_range a3 A3R.
pose proof (munch_refl [(bv_unsigned sp - RMAP_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
eapply (implF_ebind _ _ _ _ _ _ _
(fun a RNG' ms' => (a <> addr /\ 0 < a /\ a + size <= ATOP) \/ a = addr /\ exists m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
rmap_post RNG sp addr size lo m RNG' m' /\
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom bsegs))).
2: { intros a RNG' ms' [(NE & P1 & P2)|[-> PO]]; [apply UNR; [exact NE | exact P1 | exact P2]|].
destruct PO as (m' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & PO & ->).
eapply KONT. exact PO. }
iprefix.
Local Ltac2 Set LiaHints.tbl := fun () => "04g0?10439767981.76 10439767981.77 10444057070.78 10667180602.80 10835893820.80 1162083374.77  1164180522.100 11805467289.72 11805467289.73 11805467289.74 11805467289.75 11805467289.76 11805467289.77 11805467289.78 11805467289.79 11805467289.80 11833462140.99 12017784537.99 12685940462.78 12866317849.78 13084834179.78 13084834179.81 13596006226.73 13596006226.76 13725786656.82 13725786670.79 15062336688.76 15685060272.73 16581074286.78 16781328285.76 16844590268.77 16930578542.75 17098239598.76 1717300718.77  17221588796.72 17424134738.73 17424134738.76 17776320429.72 17778417576.98 17976286208.2  18689773242.77 1892362350.76  19006120615.75 19147070446.80 19365467182.99 19376804346.99 19491992743.75 19596407918.74 19622476014.72 19920749038.78 19961167854.78 20289765031.77 20894983726.99 20921468142.78 21632953838.80 21916162286.72 21931701891.80 21931701891.83 22080489625.78 22117252524.86 22163107130.78 22242271214.78 22439364775.76 22652873582.76 22749971310.76 22872305980.80 23230285244.74 23667722478.80 23909860377.78 24080369177.78 24179267756.77 24179267758.80 24451155438.76 24487705898.73 24578566572.86 24630998586.78 25025521262.76 25029166211.10125029166211.78 25071629079.99 25117511228.78 25435258127.73 25435258127.99 25566553219.75 25566553219.99 25876173099.99 25878270254.77 26000888601.77 26115614154.99 26227646574.76 26278908583.76 26436197998.76 26868428163.76 26868428163.98 27066288442.77 27198656366.78 27679091076.67 28344324846.72 28885198780.78 29212037676.20 29322360558.78 29409371564.86 29515017603.77 29515017603.78 2952178542.72  29870281326.74 30196181434.76 30231011258.78 30518562691.10030518562691.76 31086372590.79 31143001276.76 31193132057.78 31420974624.72 31521058898.73 31521058898.76 31929422315.78 31940628442.70 32440122478.74 32651489978.76 32716547054.75 32905389884.77 33227529838.76 33342412455.78 33680001082.72 34288016811.98 34290115814.66 34648577006.80 34673642734.79 35012330478.75 35082589626.78 3520940321.81  3520940335.78  35677373209.76 35938186734.77 36107562391.89 36115622435.97 36115622445.74 36367760551.78 36508527854.79 37044431129.77 37153923388.75 37496806766.78 3750459246.78  38442283758.76 38806986883.72 38806986883.98 38916199868.78 39208223342.74 39363066990.77 39530135918.76 39939624357.86 40042239854.78 40091925667.97 40091925676.75 40259044249.79 40987550979.99 41099708142.75 41317949302.98 41564619544.85 42092305134.80 4240063612.85  42501437472.10042501437472.99 42503534630.75 42505299482.70 42509314849.83 42511603879.86 42511604512.86 42511604641.85 42589343470.78 4262544750.78  42817538363.86 42831019478.73 42831019478.76 43059266230.64 43183609788.76 43231650947.80 43231650947.83 43466089753.76 43985854248.98 43987951407.74 44158664835.75 44158664835.98 44621604505.77 44752146798.76 44834901102.77 45221239098.75 46185173998.77 46232973498.76 46556098215.78 46610241646.76 46690469870.77 47196384886.99 47373904281.79 47402774638.77 47605026514.73 47605026514.76 48355031171.77 48355031171.80 48801314570.86 48817759222.99 49802719470.80 50215255347.76 50293387118.75 50862133932.77 50862133934.80 5087518190.75  50882889347.79 50882889347.82 51063395886.99 51495512430.80 51678667180.75 51680764331.99 5180980284.75  51933874855.78 52457006958.78 53324805799.79 53405636718.76 53618414247.80 53767577772.73 53769674920.98 54139164014.78 54148288295.99 54618151079.74 55104759171.74 55104759171.99 55182052846.80 55419944174.78 55467843644.79 55681940633.77 5575378989.76  5575378991.79  55837769369.80 56050883492.13 563227834.74   56759370246.7  56993697826.86 57204723438.79 5745572519.80  57756175257.80 58655119491.10058655119491.78 58762852128.82 58762852142.79 58899613550.79 59044679705.76 59178106163.73 59308628179.3  59308628566.3  59314873579.7  59314873579.8  59445865454.76 59805822339.78 59805822339.81 60341225226.84 60468873383.76 60499277734.69 60634079619.10060634079619.76 60669017326.78 61230833468.78 6165337146.79  6166287527.72  61892124754.73 61892124754.76 61917199020.75 61919296171.99 61955427318.99 62007472750.77 62131122447.76 62131122447.82 62625805991.77 62790826668.86 62826138350.72 62948418713.80 62989950816.81 62989950828.75 63235321891.97 63235321901.71 63307181686.81 63341493050.80 63473042798.78 63581907118.99 64288695406.78 64930771950.77 6501784985.78  65104334021.84 65104452412.5  65474045550.80 65759081031.69 65805175866.75 66410366446.75 66864513518.74 67258535356.76 67434480419.86 67449453465.75 67471419575.85 67642860590.99 68141967982.77 6867211502.75  778093996.86   8405736896.100 8405736896.99  8474926972.71  8539011822.80  8733664836.71  8939781870.75  9144120558.75  97018265.80    9767205155.86  00000400800A00F00J00N00R00S00T00U00V00W00X00Y00Z00[00_00`00i00j00k00l01501>01B01F01J01N01W01X01\01e01n02702;02D02M02Q02U02[02`02i02j03303<03A03B03K03T03]03f03g04004904B04K04L04M04N04R04W04`04a04j05305705;05D05E05F05J05N05W05X05\05a05j05k05l05m06106206306406506906=06>06P06Y06Z06c06d06e06j07307707@07D07Q07Z07^07_07`07i08208708<08=08>08G08K08L08P08Y08b08o09<09E09J09S09W09`09a09f09j09k0:40:=0:F0:K0:O0:S0:T0:]0:c0:g0:k0:l0;50;60;:0;C0;L0;U0;V0;W0;[0;d0;m0<60<:0<C0<G0<K0<L0<M0<V0<W0<X0<a0<b0<i0=00==0=J0=W0=^0=e0>20>;0>D0>E0>J0>O0>S0>W0>X0>Y0>Z0>^0>b0>c0>d0>e0>n0?70?<0?E0?J0?K0?T0?]0?^0?_0?h0@10@:0@;0@<0@=0@>0@G0@H0@Q0@U0@Y0@b0@c0@d0@m0A60A:0A>0AB0AC0AL0AM0AV0AW0A[0A_0Ah0Ai0Aj0Ak0Al0B50B>0BB0BC0BG0BK0BL0BQ0BV0Bf0Bj0C30C40C50C60C70C;0C?0CH0CI0CJ0CS0CZ0Ci0D;0DD0DE0DF0DG0DH0DL0DM0DN0DW0D[0D`0Da0Dj0E30E70E;0E<0EE0EF0EG0EH0EL0EU0EV0EZ0E^0Eb0Ef0Eg0El0F50F>0FG0FP0FQ0F^0Fk0G40G50G:0GC0GL0GP0G]0G^0Gc0Gl0H50H>0HB0HC0HD0HE0HN0HO0HX0Ha0Hb0HoS2LOS2LOS4CEIL2LOS3SPRS2HBS2LOS2LOSSSSSSSSSS2HBSS4CEIL2LOSSSS4CEIL2LOS4CEIL2LOS2LOS2LOS2HBS2HBS4CEIL2LOSS2HBS4CEIL2LOS4CEIL2LOS4CEIL2LOS2HBS4CEIL2LOS4CEIL2LOS2LOS2LOS4SPOSS3SPRS4CEIL2LOSS4CEIL2LOS4CEIL2LOS3SPRSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSSSS2A0S3SPRS4CEIL2LOSS4CEIL2LOS4CEIL2LOS2HBS2HBS4CEIL2LOSSS2LOS2LOS4CEIL2LOSS2A0S3SPRS4CEIL2LOSSSS2HBSSSSS2LOS2LOSS4CEIL2LO4SPOS3AM3S4CEIL2LOSS4CEIL2LOSSS3SPRS4CEIL2LOS2LOS4CEIL2LOS2HBS3SAL1H2H02H4S4CEIL2LOS2A0SSS4CEIL2LOS4CEIL2LOS3SPRS3SPRSSS4CEIL2LOS2HBSS2LOS4CEIL2LOS4CEIL2LOS4SPOS2A03ASZS4SPOS2A03ASZS4CEIL2LOS3SPRS4CEIL2LOS2HBS4CEIL2LOSS3SPRS2LOSS4CEIL2LOS4CEIL2LOS4CEIL2LOS3SPRS2LOS2LOSS4CEIL2LOS2A01HS2LOS2LOSS4CEIL2LOSS2HBS4CEIL2LOS4CEIL2LOS4CEIL2LOSSS2HBS4CEIL2LOS4CEIL2LOS4CEIL2LOS2LOS4CEIL2LOS2LOS2LOSSS4CEIL2LOSSS4CEIL2LOSS2A02K1S2A02K1S4SPOS2A03ASZS4SPOS2A03ASZS4SPOS2A03AM3S2A02K1S2A02K1S4SPOS2A03AM3S4CEIL2LOS4CEIL2LOSS3SPRS3SPRS2LOS2HBSSSS2LOS2LOSSSS4CEIL2LOS4CEIL2LOS3SPRS4CEIL2LOS3SPRSS4CEIL2LOS4CEIL2LOSSS4CEIL2LOS4CEIL2LOS4CEIL2LOSSSSS4CEIL2LOSS4CEIL2LOS2LOS2LOS4CEIL2LOSSS4CEIL2LOS4CEIL2LOS2LOS2LOS2HBSS4CEIL2LOSS4CEIL2LOSS2LOS2LOS4CEIL2LOSSSSS4CEIL2LOS4CEIL2LOS2HBSS2LOS2LOSS3AALS3SPRS4SPOS3AM23AM31HS2LOS4CEIL2LOSSSSS2LOS2LOS4CEIL2LOSSS4NAME2K0S2A02K3S4SPOS3AM32LT1HS4SPOS3AM32K11H2K2S4CEIL2LOSSSSS2LOSSS4CEIL2LOS2HBS3SPRSS4CEIL2LOS4CEIL2LOS2LOS2LOSS4CEIL2LOSSSS2A0S4CEIL2LOSS2LOS2LOS2LOS2LOSS3SPRS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSS4SPOS2A03AM3S4SPOS2A03ASZS4CEIL2LOSS3SPRS4CEIL2LOS4CEIL2LOS2HBS4CEIL2LO3AM3SS3ASZS4CEIL2LOS4CEIL2LOS4CEIL2LOS2A0FFSS4CEIL2LOSS4CEIL2LOS4CEIL2LOSS4CEIL2LO3AM3".
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
replace (ret_pc (Z_to_bv 64 419772)) with (Z_to_bv 64 419772 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
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
lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -128) _, STK : stk bsegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp + -32) end.
replace (ret_pc (Z_to_bv 64 452980)) with (Z_to_bv 64 452980 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by (clear -A0 ASZ SPOS; unfold AIMG_HI in *; lia). clear -K3 A0. lia. }
step. step. step. step. step. step.
lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -32) _, STK : stk bsegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
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
