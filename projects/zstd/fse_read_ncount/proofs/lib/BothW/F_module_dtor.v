(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import Shadow ITreeA.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg F_syscalls StdioFiles Stdio_kit MonadF F_memset AExit F_stdio_exit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StrwF SysStepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Import ITree.Exc.
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

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).
Section CANSEC1. Context {rc : runConstT}.
Definition SHOFF : Z := 0x7fff8000.
Definition shd (a : Z) : Z := SHOFF + Z.shiftr a 3.
Definition shn (l : Z) : Z := Z.shiftr l 3.
End CANSEC1.
Ltac sort_lits :=
repeat (match goal with H : rw_cells bsegs _ (Zpos ?p) _ |- _ =>
tryif (match goal with H' : rw_cells bsegs _ (Zpos ?p') _ |- _ =>
lazymatch eval vm_compute in (Z.ltb (Zpos p') (Zpos p)) with true => idtac | false => fail end end)
then fail
else (move H at bottom; lazymatch type of H with ?T => change T with (sf_hide T) in H end)
end); sf_unhide.
Ltac hstep := sort_lits; zstep; fix_lit_store.
Ltac astep := hstep; try (first [if_true | if_false]).
Ltac at_pc p := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq q p end.
Ltac steps_to p := repeat (tryif at_pc p then fail else astep).
Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Lemma unsigned_lit8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. Local Ltac2 Set LiaHints.tbl := fun () => "0010<9536388762.3000003S1H".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition mdtor_rt (m : mem) : Prop :=
rw_cells bsegs m 0x998f0 [C8 (Z_to_bv 64 0x131fe0)]
/\ rw_cells bsegs m 0x99900 [C8 (Z_to_bv 64 0x134068); C8 (Z_to_bv 64 0x9fd38); C8 (Z_to_bv 64 0xa2538);
C8 (Z_to_bv 64 0xa3228); C8 (Z_to_bv 64 0xa3230); C8 (Z_to_bv 64 0xa3220)]
/\ rw_cells bsegs m 0x99930 [C8 (Z_to_bv 64 0x9b778)]
/\ rw_cells bsegs m 0x9b770 [C8 (Z_to_bv 64 0x92c40); C8 (Z_to_bv 64 0x93044)]
/\ rw_cells bsegs m 0xa2538 [C8 (Z_to_bv 64 0x7fff8000)]
/\ rw_cells bsegs m 0xa3218 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]
/\ rw_cells bsegs m 0xa1d9c [C1 (Z_to_bv 8 1)]
/\ rw_cells bsegs m 0x1340e0 [C8 (Z_to_bv 64 0xffffffffffffffff)]
/\ rw_cells bsegs m 0x9fd50 [C4 (Z_to_bv 64 1)].
Definition rt_clear (iv : Z * Z) : Prop :=
let (lo, hi) := iv in
lo <= hi /\
(hi <= 0x998f0 \/ (0x99938 <= lo /\ hi <= 0x9b770) \/ (0x9b780 <= lo /\ hi <= 0x9fd50) \/ (0x9fd54 <= lo /\ hi <= 0xa1d9c)
\/ (0xa1d9d <= lo /\ hi <= 0xa2538) \/ (0xa2540 <= lo /\ hi <= 0xa3218) \/ (0xa321a <= lo /\ hi <= 0x1340e0) \/ 0x1340e8 <= lo).
#[using="Type"] Lemma mdtor_rt_frame : forall m m' W,
mdtor_rt m -> munch W m m' -> wmono bsegs m m' ->
Forall rt_clear W -> mdtor_rt m'.
Proof.
intros m m' W PC MU WM HW.
assert (D : forall A n, 0 <= n ->
((0x998f0 <= A /\ A + n <= 0x99938) \/ (0x9b770 <= A /\ A + n <= 0x9b780) \/ (0x9fd50 <= A /\ A + n <= 0x9fd54)
\/ (0xa1d9c <= A /\ A + n <= 0xa1d9d) \/ (0xa2538 <= A /\ A + n <= 0xa2540) \/ (0xa3218 <= A /\ A + n <= 0xa321a)
\/ (0x1340e0 <= A /\ A + n <= 0x1340e8)) -> disjoint_from W A n).
{ intros A n Hn HA. clear MU. induction HW as [|[lo hi] W H1 H2 IH]; cbn in *; [exact I|]. split; [lia| exact IH]. }
unfold mdtor_rt in *.
destruct PC as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
repeat match goal with |- _ /\ _ => split end; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply D; cbn; lia]).
Qed.
Definition poison_low_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(sb sl lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (sb, sb + sl)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp)
/\ rw_cells bsegs m' sb [CB (Z.to_nat sl) (repeat (Z_to_bv 8 0) (Z.to_nat sl))].
#[using="Type"] Lemma poison_low_spec : forall RNG (sb sl : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (addr size lo : Z) (junk : list byte),
stk bsegs m lo (bv_unsigned sp) -> KHIGH <= lo -> lo <= bv_unsigned sp - 64 ->
mem_inv bsegs m ->
mdtor_rt m ->
a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 0 ->
addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> 0x10000 <= addr -> addr + size <= 0x5f7000 -> shn size < 0x10000 ->
sb = shd addr -> sl = shn size ->
rw_cells bsegs m sb [CB (Z.to_nat sl) junk] ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG sb sl ->
evtF bsegs RNG (poison_low_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sb sl lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x54060) fc None m (seg_rom bsegs)).
Proof.
intros until junk. intros ST KH LO MI RT -> -> -> AL SL SZ LOW HIE SMALL -> -> DST RIMG RSTK RSH.
unfold KHIGH in KH. pose proof RT as RT'. destruct RT' as (PGC & GOT & GOT80 & REAL & SHB & INI & CANP & THR & RGL).
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (shd addr, shd addr + shn size)]%Z m) as MU.
pose proof (wmono_refl bsegs m) as WM.
assert (SHR : 0x7fffa000 <= shd addr /\ shd addr + shn size <= 0x800cd000 /\ 0 < shn size).
{ unfold shd, shn, SHOFF. Local Ltac2 Set LiaHints.tbl := fun () => "02O0?10143242520.10110521085166.74 10894115438.76 11041912942.76 11801259171.93 11912744615.76 12018219118.76 12367362435.76 12367362435.82 12685940462.74 13021749692.76 1527479463.74  16354687726.77 17646078182.67 17776320430.82 17776320431.75 1792056942.76  17939878638.77 18500769902.76 18736735982.77 1892362350.76  19049469500.76 19251685870.76 19618399904.87 19622476014.77 20970059894.81 21459134830.76 21875103086.76 21918414723.76 21918414723.83 23036111982.76 23483264238.74 24630998586.74 24982578106.71 24982578737.69 25025521262.76 25071629079.74 25071629079.76 25071629079.77 25167604974.76 25314760359.76 25792608750.77 25878270254.82 25878270255.75 26074863037.72 26082619953.80 27056752868.77 27335527918.76 27908601838.77 28913119922.81 29531591534.76 29717588462.76 29784417117.69 29784418006.71 29784612193.63 29786514270.73 29794353372.87 29870281326.76 31081687356.77 31466597614.74 32440122478.76 32651489978.76 32716547054.76 33039531175.77 33486665994.77 33680001082.77 34056952330.77 3517109230.77  35262033390.76 35310472686.76 35499796014.73 36115622446.76 36115622446.82 36204177774.76 3640025710.76  36423573305.95 36993589379.77 36993589379.83 37107179452.76 38889585390.77 3945979267.76  3945979267.82  39849574766.76 39996121710.76 41072247790.76 41809558659.74 41809558659.81 42501437472.87 42501437473.86 42503534633.79 42511604512.70 43060403331.77 43060403331.83 43061415849.65 43987951406.76 43987951406.82 44483185911.94 44750652170.76 45221239098.76 47178742894.76 47221216238.77 48490912238.77 48593432558.77 49343888933.95 49896851182.77 5087518190.76  51014030958.77 51481786499.76 51481786499.83 52076332701.80 5363218414.77  53767577775.75 53767577775.81 54324225646.76 55067441390.77 55419944174.74 55737922668.93 55748147788.74 55750620234.74 56007886318.76 56066145674.76 56228262055.76 563227834.76   5638167690.74  5652583082.93  57745675194.76 58732652910.76 59308628433.70 59308629336.72 59308632823.74 59310725459.73 59391397898.74 59445487498.76 59588178610.81 60025031335.77 61104133998.77 61257697518.74 61917199023.75 61917199023.81 62309656174.76 62473508590.74 62826138350.77 63235321900.73 63235321900.80 63239821294.76 63694018620.77 65098632080.78 65782973294.76 66400913390.77 66761942666.76 67800801447.76 68044863854.74 7010956092.74  8583720762.77  9155291374.74  9193927790.76  9342571886.76  985337532.76   992066670.76   00000U00\00c00j01501601=01>01?01F01J01K01R01S01W01[01b01i02002702>02B02I02J02Q02R02Y02`02a02b02i03003503603703>03?03@03A03H03I03P03T03X03d04004G04N04U04V04]04d04e04f04g04h04i05005405;05B05G05N05O05Z05_05j06106806?06@06D06H06O06V06Z06[06\06`06g06h06i07007707>07?07@07H07P07\07h07i07j07n08208608>08I08N08U08\08c08j08k09209909@09A09B09C09J09N09R09Y09`09g0:20:=0:H0:O0:Z0:[0:`0:e0:j0:o0;60;A0;I0;S0;X0;c0;n0;o0<00<70<>0<B0<F0<M0<T0<[0<_0<c0<j0<n0=:0=A0=H0=S0=T0=[0=_0=d0=k0>20>90>=0>DS2AL2SL2SZ3LOW3HIE1H2H02H42H93H143H15S2KH2LOS2KH2LOS2KH2LOS2KH2LO3SHRSS2KH2LOSSS2KH2LOS2HBSS2KH2LOSS2LOS2LOS2KH2LOS2KH2LOS2KH2LOS2KH2LOS2KH2LOS2HBS2KH2LOFS2KH2LOSS2KH2LOS2KH2LOSSS2KH2LOS2KH2LOS3RSPSSS2KH2LOSSSS2KH2LOSS2KH2LOS2LOS2LOS2SZ3LOW3HIES2SZ3LOW3HIES2AL2SL2SZ3LOW3HIE1H2H4S2KH2LOS2KH2LOSS2KH2LOS2KH2LOSSSSSS2KH2LOS2HBS2KH2LOS2KH2LOS3RSPS2KH2LOSS2KH2LO3SHRS3RSPS2KH2LO3SHRS2KH2LOS2KH2LOS2KH2LOSS2LOS2LOS2KH2LOS2KH2LOS2LOSSS2HBS2KH2LOSSS2KH2LOS2KH2LOS2KH2LOSSS3LOW2K2S3LOW2K2S2SZ3LOW3HIES2SZ3LOW3HIESSS2LOS2LOS2LOS2KH3SHRS2KH2LO3SHRS3RSPS2KH2LOS2KH2LOS2KH2LOS2KH2LOSS2KH2LOS2KH2LOS2KH2LOSSFS2KH2LOS2LOS2LOS2KH2LOS2KH2LOS2KH2LOS5SMALL3SHRS5SMALL3SHRS5SMALL3SHRS2KH2LOS2KH2LO3SHRSS3RSPS3SHRS3SHRS3RSPS2KH2LOS2SZ3HIE2K2S3HIE2K9S5SMALL2KTS3K10S2KH2LO3SHRS2KH2LO3SHRSSS2KH2LOS2KH2LOS2LOS2LOS2KH2LOS2KH2LOS2KH2LOS2LOS2LOS2KH2LOS2HBS2SZ3LOW3HIES2KH2LOS2KH2LOS2KH2LO3SHRSS2KH2LOS2HBS3RSPS2KH2LOS2KH2LOS2KH2LOS2HBS2KH2LO".
rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
carve_frame 64%nat ST.
do 8 hstep.
hstep. if_true.
zstep. hstep. if_cases K1; zify_cond K1.
{ exfalso. apply K1. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact AL. }
do 3 hstep.
do 4 zstep.
match goal with |- context [Z.land ?x 2147450879] => let v := eval vm_compute in (Z.land x 2147450879) in change (Z.land x 2147450879) with v end.
hstep. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }
zstep. hstep. if_cases K8; zify_cond K8.
{ exfalso. apply K8. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact SL. }
do 2 zstep.
hstep. if_cases K9; zify_cond K9. 2:{ exfalso. lia. }
do 3 hstep.
hstep. if_cases K10; zify_cond K10; [exfalso; lia|].
do 5 zstep.
assert (E1 : Z.land (Z.shiftr (addr + size + -8) 3 + 1) 18446744073709551615 - Z.shiftr addr 3 = shn size).
{ unfold shn. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. change 18446744073709551615 with (Z.ones 64).
rewrite Z.land_ones by lia. change (2 ^ 64) with 18446744073709551616. Z.div_mod_to_equations. lia. }
rewrite E1. clear E1. change (2147450880 + Z.shiftr addr 3) with (shd addr).
hstep. if_false.
do 3 hstep.
hstep. if_cases KT; zify_cond KT.
2:{ exfalso. lia. }
do 3 hstep. do 8 hstep.
hstep.
eapply evtF_mono.
{ eapply memset_spec; [ rewrite !unsigned_lit by lia; exact DST | exact MI | rewrite !unsigned_lit by lia; exact RSH ]. }
intros ms' PO. unfold memset_post in PO. unfold poison_low_post. destruct_exs PO.
destruct PO as (-> & MU2 & WM2 & MI2 & DST2).
rewrite !unsigned_lit in MU2, DST2 by lia. change (0 mod 256) with 0 in DST2.
do 16 eexists. split; [reflexivity|].
split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. intros xq Hxq. cbn in Hxq |- *. tauto. }
split. { eapply wmono_trans; [exact WM| exact WM2]. }
split. { exact MI2. }
split. 2: exact DST2.
pose proof (rw_cells_transport bsegs _ _ _ _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize]; lia)) as FR'.
pose proof (stk_transport_disjoint bsegs _ _ _ _ _ ST MU2 WM2 ltac:(cbn [disjoint_from]; lia)) as ST'.
eapply stk_release in FR'; [| exact ST' | lia]. cbn [cells_size csize Nat.add] in FR'.
match type of FR' with stk _ _ _ ?hi => replace hi with (bv_unsigned sp) in FR' by lia end. exact FR'.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition unreg_one_post (spv d sb sl : Z) (gp tp s5 s6 s8 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
: machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR (Z_to_bv 64 0x40374) (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x134068) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 2) (Z_to_bv 64 0x1b2e8) (Z_to_bv 64 d) s5 s6 (Z_to_bv 64 0x9b778) s8 (Z_to_bv 64 0x9fd38)
(Z_to_bv 64 0xa2538) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x40374) fc None m' (seg_rom bsegs)
/\ munch [(sb, sb + sl)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ rw_cells bsegs m' sb [CB (Z.to_nat sl) (repeat (Z_to_bv 8 0) (Z.to_nat sl))].
#[using="Type"] Lemma unreg_one_spec : forall RNG (sb sl : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s8 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) fc (m : mem) (spv d beg swr : Z) (gsz gnm gmd gdy glc godr : word) (junk : list byte),
mem_inv bsegs m -> mdtor_rt m ->
rw_cells bsegs m d [C8 (Z_to_bv 64 beg); C8 gsz; C8 (Z_to_bv 64 swr); C8 gnm; C8 gmd; C8 gdy; C8 glc; C8 godr] ->
rw_cells bsegs m (d + 16) [C1 (Z_to_bv 8 swr)] ->
beg mod 8 = 0 -> swr mod 8 = 0 -> 0 < swr < 256 -> 0x10000 <= beg -> beg + swr <= 0x5f7000 ->
0x10000 <= d -> d + 64 <= 0x5f7000 -> 0 <= spv < 2^64 ->
sb = shd beg -> sl = shn swr ->
rw_cells bsegs m sb [CB (Z.to_nat sl) junk] ->
rng_aimg RNG -> rng RNG sb sl ->
evtF bsegs RNG (unreg_one_post spv d sb sl gp tp s5 s6 s8 s11 F fc m)
(MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x134068) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 2) (Z_to_bv 64 0x1b2e8) (Z_to_bv 64 d) s5 s6 (Z_to_bv 64 0x9b778) s8 (Z_to_bv 64 0x9fd38)
(Z_to_bv 64 0xa2538) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x4038c) fc None m (seg_rom bsegs)).
Proof.
intros until junk. intros MI RT D DB AL SL SWR LOW HIE DLO DHI SPV -> -> DST RIMG RSH.
pose proof RT as RT'. destruct RT' as (PGC & GOT & GOT80 & REAL & SHB & INI & CANP & THR & RGL).
pose proof (munch_refl [(shd beg, shd beg + shn swr)]%Z m) as MU.
pose proof (wmono_refl bsegs m) as WM.
assert (SHR : 0x7fffa000 <= shd beg /\ shd beg + shn swr <= 0x800cd000 /\ 0 < shn swr < 32).
{ unfold shd, shn, SHOFF. Local Ltac2 Set LiaHints.tbl := fun () => "00\0>10009457963.7710009457963.8019620497065.8020970059894.7824115025141.8024982578487.6824982578614.6926082619952.7728913119920.8029001722024.7629001722024.7929071941542.8229601281241.6829784416347.6829784416474.6929784612193.6529786758908.6930422568588.7030424711306.7030426549930.8933161241475.7834309704694.7535499809676.6941209397009.7942396708221.7948107158204.8948109515932.704860049526.72 51563130523.8152076332688.7452076332702.7653510313876.7754805412144.8955047472860.7859308628433.6759308632823.7059588178608.8060996812196.8163674995624.7563677092781.8263683735724.6764713536689.7664713536689.798506398648.10400000100200300400500600700D00E00F00G00H00M00N00O00P00Q00V00[00`00a00b00c00d01<01A01F01G01H01I01J01K01L01U01a01i01j02302;02C02P02Y02b03PSSFSFSSS3SWR3LOW3HIESFFFS3SWRSSSSS3SHRS3SHRS3SHRFSSSS2AL2SL3SWR3LOW3HIE1H2H4S3SHRS3SHRSFFFSSS3DLO3DHIS3SWR3HIE2K2S3SHR2KTSS3DLO3DHIS3LOW2K2S3LOW2K2S3SWR3LOW3HIES3DLO3DHIS3DLO3DHIS2AL2SL3SWR3LOW3HIE1H2H02H42H93H143H153H193H20".
rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
do 7 hstep.
hstep. if_false.
hstep.
replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (vm_compute; reflexivity).
hstep. if_true.
hstep. if_false.
do 2 hstep. do 4 zstep.
match goal with |- context [Z.land ?x 2147450879] => let v := eval vm_compute in (Z.land x 2147450879) in change (Z.land x 2147450879) with v end.
hstep. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }
zstep. hstep. if_cases K3; zify_cond K3.
{ exfalso. apply K3. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact AL. }
hstep. zstep. rewrite (unsigned_lit8 swr) by lia. hstep. if_cases K4; zify_cond K4.
{ exfalso. apply K4. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact SL. }
do 6 hstep. hstep. if_false.
do 3 hstep. do 5 zstep. hstep. do 3 zstep.
assert (E1 : Z.land (2147450880 + Z.shiftr (beg + swr + -8) 3 + 1) 18446744073709551615 - Z.land (2147450880 + Z.shiftr beg 3) 18446744073709551615
= shn swr).
{ unfold shn. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. change 18446744073709551615 with (Z.ones 64).
rewrite !Z.land_ones by lia. change (2 ^ 64) with 18446744073709551616. Z.div_mod_to_equations. lia. }
rewrite E1. clear E1. change (2147450880 + Z.shiftr beg 3) with (shd beg).
hstep. if_cases KT; zify_cond KT. 2:{ exfalso. lia. }
do 3 hstep.
eapply evtF_mono.
{ eapply memset_spec; [ rewrite !unsigned_lit by lia; exact DST | exact MI | rewrite !unsigned_lit by lia; exact RSH ]. }
intros ms' PO. unfold memset_post in PO. unfold unreg_one_post. destruct_exs PO.
destruct PO as (-> & MU2 & WM2 & MI2 & DST2).
rewrite !unsigned_lit in MU2, DST2 by lia. change (0 mod 256) with 0 in DST2.
cbn [ret_pc reg_get].
replace (ret_pc (Z_to_bv 64 0x40374)) with (Z_to_bv 64 0x40374 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
do 17 eexists. split; [reflexivity|].
split. { eapply munch_trans; [exact MU|]. exact MU2. }
split. { eapply wmono_trans; [exact WM| exact WM2]. }
split. { exact MI2. }
exact DST2.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition gdesc (m : mem) (d beg sz swr nm md odr : Z) : Prop :=
rw_cells bsegs m d [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 swr); C8 (Z_to_bv 64 nm); C8 (Z_to_bv 64 md);
C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 odr)]
/\ rw_cells bsegs m (d + 16) [C1 (Z_to_bv 8 swr)].
Definition AGLOBALS : list (Z * Z * Z * Z * Z) := [
(0x20e60, 36, 96, 0x1c0d5, 0x20e0b);
(0x20ec0, 65, 128, 0x1e838, 0x20e0b);
(0x20f40, 1, 32, 0x2059d, 0x20e0b);
(0x20f60, 24, 64, 0x147e5, 0x20e0b);
(0x20fa0, 26, 64, 0x1374b, 0x20e0b);
(0x20fe0, 25, 64, 0x1d081, 0x20e0b);
(0x21020, 37, 96, 0x1883b, 0x20e0b);
(0x21080, 25, 64, 0x1a53c, 0x20e0b);
(0x210c0, 27, 64, 0x113a4, 0x20e0b);
(0x212c0, 23, 64, 0x1c0d5, 0x21e40);
(0x21300, 18, 64, 0x1e838, 0x21e40);
(0x21340, 16, 32, 0x2059d, 0x21e40);
(0x21360, 25, 64, 0x147e5, 0x21e40);
(0x213a0, 22, 64, 0x1374b, 0x21e40);
(0x213e0, 28, 64, 0x1d081, 0x21e40);
(0x21420, 44, 96, 0x1883b, 0x21e40);
(0x21480, 25, 64, 0x1a53c, 0x21e40);
(0x214c0, 37, 96, 0x113a4, 0x21e40);
(0x21520, 63, 96, 0x166fb, 0x21e40);
(0x21580, 22, 64, 0x1f8d1, 0x21e40);
(0x215c0, 38, 96, 0x113ab, 0x21e40);
(0x21620, 26, 64, 0x19ea3, 0x21e40);
(0x21660, 29, 64, 0x1f8d9, 0x21e40);
(0x216a0, 37, 96, 0x1ddb0, 0x21e40);
(0x21700, 37, 96, 0x1c0da, 0x21e40);
(0x21760, 53, 96, 0x1975d, 0x21e40);
(0x217c0, 48, 96, 0x1b93c, 0x21e40);
(0x21820, 41, 96, 0x11b56, 0x21e40);
(0x21880, 38, 96, 0x11b5e, 0x21e40);
(0x218e0, 48, 96, 0x17e4d, 0x21e40);
(0x21940, 52, 96, 0x19eab, 0x21e40);
(0x219a0, 24, 64, 0x147ec, 0x21e40);
(0x219e0, 20, 64, 0x13d3b, 0x21e40);
(0x21a20, 47, 96, 0x13752, 0x21e40);
(0x21a80, 32, 64, 0x16f25, 0x21e40);
(0x21ac0, 22, 64, 0x10add, 0x21e40);
(0x21b00, 37, 96, 0x17e55, 0x21e40);
(0x21b60, 80, 128, 0x17634, 0x21e40);
(0x21be0, 73, 128, 0x10ae5, 0x21e40);
(0x21c60, 25, 64, 0x1375a, 0x21e40);
(0x21ca0, 43, 96, 0x113b3, 0x21e40);
(0x21d00, 28, 64, 0x123b7, 0x21e40);
(0x21d40, 23, 64, 0x13d43, 0x21e40);
(0x21d80, 62, 96, 0x1ddb8, 0x21e40);
(0x21de0, 33, 96, 0x17e5d, 0x21e40);
(0x21ee0, 36, 96, 0x1c0d5, 0x21e99);
(0x21f40, 13, 32, 0x1e838, 0x21e99);
(0x21f60, 1, 32, 0x2059d, 0x21e99);
(0x21f80, 36, 96, 0x1c0d5, 0x21fe0);
(0x22020, 6, 32, 0x2059d, 0x21fe0);
(0x22040, 1, 32, 0x147e5, 0x21fe0)]%Z.
Fixpoint gdescs (m : mem) (d : Z) (G : list (Z * Z * Z * Z * Z)) : Prop :=
match G with
| [] => True
| (b, sz, swr, nm, md) :: G' => gdesc m d b sz swr nm md (2^64 - 1) /\ gdescs m (d + 64) G'
end.
Fixpoint gsorted (lo hi : Z) (G : list (Z * Z * Z * Z * Z)) : Prop :=
match G with
| [] => True
| (b, sz, swr, nm, md) :: G' =>
lo <= shd b /\ shd b + shn swr <= hi /\ b mod 8 = 0 /\ swr mod 8 = 0 /\ 0 < swr < 256 /\ 0x10000 <= b /\ b + swr <= 0x5f7000
/\ gsorted (shd b + shn swr) hi G'
end.
Fixpoint gshads (m : mem) (G : list (Z * Z * Z * Z * Z)) : Prop :=
match G with
| [] => True
| (b, sz, swr, nm, md) :: G' => (exists j, rw_cells bsegs m (shd b) [CB (Z.to_nat (shn swr)) j]) /\ gshads m G'
end.
Fixpoint gsortedb (lo hi : Z) (G : list (Z * Z * Z * Z * Z)) : bool :=
match G with
| [] => true
| (b, sz, swr, nm, md) :: G' =>
(lo <=? shd b) && (shd b + shn swr <=? hi) && (b mod 8 =? 0) && (swr mod 8 =? 0) && (0 <? swr) && (swr <? 256)
&& (0x10000 <=? b) && (b + swr <=? 0x5f7000) && gsortedb (shd b + shn swr) hi G'
end.
#[using="Type"] Lemma gsortedb_ok : forall G lo hi, gsortedb lo hi G = true -> gsorted lo hi G.
Proof.
induction G as [|[[[[b sz] swr] nm] md] G IH]; intros lo hi H; cbn [gsortedb gsorted] in *; [exact I|].
repeat rewrite andb_true_iff in H. destruct H as [[[[[[[[H1 H2] H3] H4] H5] H6] H7] H8] H9].
apply Z.leb_le in H1, H2, H7, H8. apply Z.eqb_eq in H3, H4. apply Z.ltb_lt in H5, H6.
repeat split; try assumption; try lia. apply IH. exact H9.
Qed.
#[using="Type"] Lemma AGLOBALS_sorted : gsorted 0x7fffc1cc 0x7fffc40c AGLOBALS.
Proof. apply gsortedb_ok. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma AGLOBALS_length : Z.of_nat (length AGLOBALS) = 51.
Proof. reflexivity. Qed.
#[using="Type"] Lemma cb_sub : forall m a (k : nat) j a' n', rw_cells bsegs m a [CB k j] -> a <= a' -> 0 <= n' -> a' + n' <= a + Z.of_nat k ->
exists j', rw_cells bsegs m a' [CB (Z.to_nat n') j'].
Proof.
intros m a k j a' n' [[WF [A0 [AL BY]]] [W0 [W1 W]]] H1 H2 H3.
cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize] in *. destruct WF as [LJ _]. rewrite app_nil_r in *. rewrite Nat.add_0_r in *.
exists (firstn (Z.to_nat n') (skipn (Z.to_nat (a' - a)) j)).
assert (LEN : length (firstn (Z.to_nat n') (skipn (Z.to_nat (a' - a)) j)) = Z.to_nat n').
{ rewrite length_firstn, length_skipn. Local Ltac2 Set LiaHints.tbl := fun () => "0070>2110276096.20 26788613325.1733553799239.1844398370564.2048937938509.1851361431095.2058982491506.2000000;00E00V00j01801I01WS2LJ3LEN2HiS2LJ2H12H3S2LJ2W12H22H33LENS2LJ2H12H22H33LEN2HiS2LJ2W02H13LENS2LJ2H12H33LEN2HiS2LJ2H13LEN2Hi".
lia. }
split; [split|].
- cbn [cells_wf cell_wf]. split; [exact LEN| exact I].
- cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [rewrite LEN; lia|].
intros i Hi. rewrite LEN in Hi.
rewrite nth_error_firstn. replace (Nat.ltb i (Z.to_nat n')) with true by (symmetry; apply Nat.ltb_lt; exact Hi). rewrite nth_error_skipn.
replace (a' + Z.of_nat i) with (a + Z.of_nat (Z.to_nat (a' - a) + i)) by lia. apply BY. lia.
- cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|]. intros i Hi.
replace (a' + i) with (a + (a' - a + i)) by lia. apply W. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma gshads_of_hull : forall G lo hi m a (k : nat) j, rw_cells bsegs m a [CB k j] -> a <= lo -> hi <= a + Z.of_nat k ->
gsorted lo hi G -> gshads m G.
Proof.
induction G as [|[[[[b sz] swr] nm] md] G IH]; intros lo hi m a k j C H1 H2 S; cbn [gshads gsorted] in *; [exact I|].
destruct S as (L1 & L2 & _ & _ & SW & _ & _ & S).
Local Ltac2 Set LiaHints.tbl := fun () => "0060>12602440416.2229782446203.2143839256185.2158324979654.2263577466763.22748780348.21  00000700800<00F00M00NS2H22L2SS2SWS2H12L12N0S2H12L1S".
assert (N0 : 0 <= shn swr) by (unfold shn; rewrite Z.shiftr_div_pow2 by lia; apply Z.div_pos; lia).
split.
- eapply cb_sub; [exact C| lia| exact N0| lia].
- eapply IH; [exact C| | exact H2| exact S]. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma gdescs_transport : forall G W m m' d, gdescs m d G -> munch W m m' -> wmono bsegs m m' ->
(forall A n, d <= A -> 0 <= n -> A + n <= d + 64 * Z.of_nat (length G) -> disjoint_from W A n) -> gdescs m' d G.
Proof.
induction G as [|[[[[b sz] swr] nm] md] G IH]; intros W m m' d HG MU WM HD; cbn [gdescs length] in *; [exact I|].
destruct HG as [[D1 D2] HG]. split; [split|].
- Local Ltac2 Set LiaHints.tbl := fun () => "0090>12128333532.1817451922806.182424953317.23 28082131295.183080755707.23 33669200788.1841912482204.2346585200585.1868059072559.1800000100200600700;00<00@00A00BSSS2H2SS2H3SS2H1SS".
eapply rw_cells_transport; [exact D1| exact MU| exact WM| apply HD; cbn [cells_size csize Nat.add]; lia].
- eapply rw_cells_transport; [exact D2| exact MU| exact WM| apply HD; cbn [cells_size csize Nat.add]; lia].
- eapply IH; [exact HG| exact MU| exact WM|]. intros A n H1 H2 H3. apply HD; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma gshads_transport : forall G W m m' lo hi, gshads m G -> gsorted lo hi G -> munch W m m' -> wmono bsegs m m' ->
(forall A n, lo <= A -> 0 <= n -> A + n <= hi -> disjoint_from W A n) -> gshads m' G.
Proof.
induction G as [|[[[[b sz] swr] nm] md] G IH]; intros W m m' lo hi HG S MU WM HD; cbn [gshads gsorted] in *; [exact I|].
destruct HG as [[j C] HG]. destruct S as (L1 & L2 & _ & _ & SW & _ & _ & S).
Local Ltac2 Set LiaHints.tbl := fun () => "0090>15875498245.242424953317.29 29784463594.2343845369576.2344206882378.2452369040876.2457491806763.2964576884989.24751285165.23  00000400800900=00A00E00O00P00QS2L1S2H2SS2SWS2L2S2N0S2L12N02H1SS".
assert (N0 : 0 <= shn swr) by (unfold shn; rewrite Z.shiftr_div_pow2 by lia; apply Z.div_pos; lia).
split.
- exists j. eapply rw_cells_transport; [exact C| exact MU| exact WM|]. apply HD; [lia| lia|]. cbn [cells_size csize].
rewrite Nat.add_0_r, Z2Nat.id by lia. lia.
- eapply IH; [exact HG| exact S| exact MU| exact WM|]. intros A n H1 H2 H3. apply HD; [lia| lia| exact H3].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition mdtor_pre (m : mem) : Prop :=
mdtor_rt m
/\ rw_cells bsegs m 0x9a590 [C8 (Z_to_bv 64 0x9e1c0); C8 (Z_to_bv 64 0x9ee80)]
/\ rw_cells bsegs m 0x9ee80 [C8 (Z_to_bv 64 1)]
/\ rw_cells bsegs m 0x9fdf0 [C8 (Z_to_bv 64 0)]
/\ gdescs m 0x9e1c0 AGLOBALS
/\ (exists j, rw_cells bsegs m 0x7fffc1cc [CB 576 j])
/\ (exists j, rw_cells bsegs m 0x8000bc38 [CB 408 j]).
#[using="Type"] Lemma mdtor_pre_frame : forall sp m m',
mdtor_pre m -> KHIGH <= sp - 48 - MDTOR_DEPTH -> munch (AEXIT_W1 sp) m m' -> wmono bsegs m m' -> mdtor_pre m'.
Proof.
intros sp m m' P KH MU WM. unfold KHIGH, MDTOR_DEPTH in KH.
assert (D : forall A n, 0 <= n -> A + n <= 0x80014330 -> 0x5f5744 <= A \/ (0x9eed1 <= A /\ A + n <= 0x5f5520) \/ A + n <= 0x9eed0 ->
disjoint_from (AEXIT_W1 sp) A n).
{ intros A n Hn HA HO. unfold AEXIT_W1, MDTOR_DEPTH. cbn. Local Ltac2 Set LiaHints.tbl := fun () => "00E0>12651472574.1819594727870.182424953317.23 28279534036.1728337422245.1329252783358.1833670935481.1834180409523.1840553439155.1841967516478.1846927705117.1747210600349.1749587500189.175636646045.17 58634885427.1862695902398.1863063375389.1765435686003.1868583154407.236892662769.23 8458439091.18 00000100200600:00D00E00F00G00H00I00J00K00L00M00N00O00P00Q00U00Y00ZSSS2H2S2KHS2KH2HA2HOSSSSSSSSSSSSSS2H3S2H3S".
lia. }
unfold mdtor_pre in *.
destruct P as (RT & G1 & G2 & G3 & GD & [j1 S1] & [j2 S2]).
assert (RT' : mdtor_rt m').
{ eapply mdtor_rt_frame; [exact RT | exact MU | exact WM | ]. unfold AEXIT_W1, MDTOR_DEPTH.
repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
refine (conj RT' _).
split; [| split; [| split; [| split; [| split]]]].
- eapply rw_cells_transport; [exact G1 | exact MU | exact WM | apply D; cbn; lia].
- eapply rw_cells_transport; [exact G2 | exact MU | exact WM | apply D; cbn; lia].
- eapply rw_cells_transport; [exact G3 | exact MU | exact WM | apply D; cbn; lia].
- eapply gdescs_transport; [exact GD | exact MU | exact WM |]. rewrite AGLOBALS_length. intros A n H1 H2 H3. apply D; lia.
- exists j1. eapply rw_cells_transport; [exact S1 | exact MU | exact WM | apply D; cbn; lia].
- exists j2. eapply rw_cells_transport; [exact S2 | exact MU | exact WM | apply D; cbn; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC2.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac rt_split := unfold mdtor_rt; repeat match goal with |- _ /\ _ => split end; hyp_by_addr.
Ltac lit_nat := repeat match goal with H : rw_cells _ _ _ [CB (Z.to_nat (Zpos ?p)) _] |- _ =>
let v := eval vm_compute in (Z.to_nat (Zpos p)) in change (Z.to_nat (Zpos p)) with v in H; move H at top end.
Ltac lit_rng := repeat match goal with H : rng _ _ (Zpos ?a - Zpos ?b) |- _ =>
let v := eval vm_compute in (Zpos a - Zpos b) in change (Zpos a - Zpos b) with v in H end.
Ltac side RIMG RSTK KH :=
lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- rng _ _ _ => first [ assumption | eapply rng_sub'; [exact RSTK | lia] ]
| |- rng_aimg _ => exact RIMG
| |- rw_cells _ _ (?a + ?b) _ => let v := eval vm_compute in (a + b) in change (a + b) with v; hyp_by_addr
| |- rw_cells _ _ _ _ => hyp_by_addr
| |- mdtor_rt _ => rt_split
| |- mem_inv _ _ => hyp_by_addr
| |- stk _ _ _ _ => hyp_by_addr
| |- @eq _ _ _ => reflexivity
| |- Z.lt (shn _) _ => vm_compute; reflexivity
| |- _ => first [exact KH | lia]
end.
Ltac hstepS := sort_lits; zstep; fix_lit_store.
Ltac astepS := hstepS; try (first [if_true | if_false]).
Section CANSEC2b. Context {rc : runConstT}.
#[using="Type"] Lemma munch_hull : forall lo hi a b m m', munch [(a, b)] m m' -> lo <= a -> b <= hi -> munch [(lo, hi)] m m'.
Proof.
intros lo hi a b m m' M H1 H2. eapply munch_weaken; [| exact M]. unfold sub_fp. intros x Hx. cbn [outside] in *.
destruct Hx as [Hx _]. Local Ltac2 Set LiaHints.tbl := fun () => "0010>40231916450.1200000:S2H12H22Hx".
split; [lia| exact I].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma munch_hull2 : forall lo hi a b m m1 m', munch [(lo, a)] m m1 -> munch [(b, hi)] m1 m' -> lo <= b -> a <= hi -> munch [(lo, hi)] m m'.
Proof.
intros lo hi a b m m1 m' M1 M2 H H'. eapply munch_trans; [eapply munch_weaken; [| exact M1] | eapply munch_weaken; [| exact M2]];
unfold sub_fp; intros x Hx; cbn [outside] in *; destruct Hx as [Hx _]; split; try exact I; lia.
Qed.
#[using="Type"] Lemma unreg_loop : forall G RNG (lo hi d spv : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s8 t3 t4 t5 t6 : word)
(F : bvmap 5 word) fc (m : mem),
G <> [] ->
mem_inv bsegs m -> mdtor_rt m -> gdescs m d G -> gshads m G -> gsorted lo hi G ->
0x10000 <= d -> d + 64 * Z.of_nat (length G) <= 0x5f7000 -> 0x7fffa000 <= lo -> hi <= 0x800cd000 -> 0 <= spv < 2^64 ->
rng_aimg RNG -> rng RNG lo (hi - lo) ->
evtF bsegs RNG (fun ms' => exists (ra' t0' t1' t2' s0' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
ms' = MS (mkR ra' (Z_to_bv 64 spv) gp tp t0' t1' t2' s0' (Z_to_bv 64 0x134068) a0' a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 2) (Z_to_bv 64 0x1b2e8) (Z_to_bv 64 (d + 64 * Z.of_nat (length G))) s5 s6 (Z_to_bv 64 0x9b778) s8
(Z_to_bv 64 0x9fd38) (Z_to_bv 64 0xa2538) (Z_to_bv 64 0) t3' t4' t5' t6')
F (Z_to_bv 64 0x40590) fc None m' (seg_rom bsegs)
/\ munch [(lo, hi)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m')
(MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x134068) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 2) (Z_to_bv 64 0x1b2e8) (Z_to_bv 64 d) s5 s6 (Z_to_bv 64 0x9b778) s8 (Z_to_bv 64 0x9fd38)
(Z_to_bv 64 0xa2538) (Z_to_bv 64 (Z.of_nat (length G))) t3 t4 t5 t6)
F (Z_to_bv 64 0x4038c) fc None m (seg_rom bsegs)).
Proof.
induction G as [|[[[[b sz] swr] nm] md] G IH]; intros until m; intros NE MI RT HD HS HSO D0 D1 LO HI SPV RIMG RH; [congruence|].
clear NE. cbn [gdescs gshads length] in *. pose proof HSO as HSO'. cbn [gsorted] in HSO'.
destruct HD as [[DC DB] HD]. destruct HS as [[j SH] HS]. destruct HSO' as (L1 & L2 & AL & SL & SW & BL & BH & HSO').
rewrite Nat2Z.inj_succ in D1 |- *.
pose proof (Zle_0_nat (length G)) as LG.
Local Ltac2 Set LiaHints.tbl := fun () => "00X0?11150279611.66 11925954779.88 14892681432.96 15306844775.96 15873449912.93 15877545095.11718375735985.90 19301059053.96 22063674542.66 2424953317.94  2728801115.66  27616505739.66 29603282131.66 29784530535.63 30090030831.96 30096696442.66 33669004442.87 33935627387.66 34506992316.87 35070535434.95 35253210252.96 37431855784.66 37529455908.93 38610020951.95 44200493303.93 44204786632.11747404309994.11747988827160.64 48701252342.96 52061149739.94 54612051697.94 54917223859.10257829424363.65 59709448941.11762512989918.11766110553915.10266985707007.77 67413269194.93 67770632493.1027853444906.96  00000700>00B00I00M00Q00[00\00`00d00h00l01001101601;01<01@01G01J01N01R01S01W01[01_01`01g02102;02B02C02J02K02R02S02\02_02i02mS2D12LGS2N02SBS2D1S2L12N0S2L1S2L1S2LO2L12HASS2D0S2H2S2ALS2SLS2SWSS3SPVS3SPVSS2BHS2D12LGS1KS2D0S2BLFS2H1S2L2S2L2SS2LO2L1S2LO2L12N0S2D02D12LGS2D12H3FS2L12L2SS2L12N0FS2SL2SW1HS1KS2D02D12LGS2HI".
assert (N0 : 0 < shn swr < 32) by (unfold shn; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
assert (SB : 0x7fffa000 <= shd b) by lia.
assert (RX : rng RNG (shd b) (shn swr)) by (eapply rng_sub'; [exact RH| lia]).
change (2^64 - 1) with 18446744073709551615 in DC.
eapply evtF_cut.
{ eapply (unreg_one_spec RNG (shd b) (shn swr)); first [exact MI | exact RT | exact DC | exact DB | exact SH | exact RIMG | exact RX
| reflexivity | lia]. }
intros ms1 PO1. unfold unreg_one_post in PO1.
destruct PO1 as (t0' & t1' & t2' & s0' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & _).
assert (DJ : forall A n, 0 <= n -> A + n <= 0x5f7000 -> disjoint_from [(shd b, shd b + shn swr)] A n).
{ intros A n Hn HA. cbn [disjoint_from]. split; [left; lia| exact I]. }
pose proof (rw_cells_transport bsegs _ _ _ _ _ DC MU1 WM1 ltac:(apply DJ; cbn [cells_size csize Nat.add]; lia)) as DC1.
assert (RT1 : mdtor_rt m1).
{ eapply mdtor_rt_frame; [exact RT| exact MU1| exact WM1|]. apply Forall_cons; [| apply Forall_nil]. cbn [rt_clear]. lia. }
assert (HD1 : gdescs m1 (d + 64) G).
{ eapply gdescs_transport; [exact HD| exact MU1| exact WM1|]. intros A n H1 H2 H3. apply DJ; lia. }
assert (HS1 : gshads m1 G).
{ eapply gshads_transport; [exact HS| exact HSO'| exact MU1| exact WM1|]. intros A n H1 H2 H3. cbn [disjoint_from]. split; [right; lia| exact I]. }
clear DC DB SH HD HS RT MI.
pose proof RT1 as RT1'. destruct RT1' as (PGC & GOT & GOT80 & REAL & SHB & INI & CANP & THR & RGL).
hstepS. hstepS. astepS. hstepS. hstepS. hstepS.
if_cases K; zify_cond K.
-
destruct G as [|g G]; [| cbn [length] in K; rewrite Nat2Z.inj_succ in K; lia].
apply evtF_done. cbn [length]. do 18 eexists.
split; [reflexivity|].
split; [eapply munch_hull; [exact MU1| lia| lia]|]. split; [exact WM1| exact MI1].
-
destruct G as [|g G]; [cbn [length] in K; lia|].
set (G' := g :: G) in *.
match goal with |- context [Z_to_bv 64 (Z.succ (Z.of_nat (length G')) + ?c)] =>
replace (Z_to_bv 64 (Z.succ (Z.of_nat (length G')) + c)) with (Z_to_bv 64 (Z.of_nat (length G'))) by (f_equal; lia) end.
eapply evtF_mono.
{ eapply (IH RNG (shd b + shn swr) hi (d + 64)); first [ discriminate | exact MI1 | exact RT1 | exact HD1 | exact HS1 | exact HSO'
| exact RIMG | eapply rng_sub'; [exact RH| lia] | lia ]. }
cbv beta. intros ms' (ra' & t0'' & t1'' & t2'' & s0'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m' & -> & MU2 & WM2 & MI2).
exists ra', t0'', t1'', t2'', s0'', a0'', a1'', a2'', a3'', a4'', a5'', a6'', a7'', t3'', t4'', t5'', t6'', m'.
split; [ match goal with |- context [Z_to_bv 64 (d + 64 * Z.succ (Z.of_nat (length G')))] =>
replace (d + 64 * Z.succ (Z.of_nat (length G'))) with (d + 64 + 64 * Z.of_nat (length G')) by lia end;
reflexivity |].
split; [eapply (munch_hull2 lo hi (shd b + shn swr) (shd b + shn swr)); [eapply munch_hull; [exact MU1| lia| lia] | exact MU2 | lia | lia]|].
split; [eapply wmono_trans; [exact WM1| exact WM2]| exact MI2].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC2b.
Ltac hstep ::= zstep; fix_lit_store.
Section CANSEC3. Context {rc : runConstT}.
#[using="Type"] Theorem module_dtor_proof : module_dtor_stmt mdtor_pre.
Proof.
unfold module_dtor_stmt. intros until lo. intros HPRE ST LO KH MI RSTK RIMG RW.
pose proof KH as KH'. unfold KHIGH in KH'. unfold MDTOR_DEPTH in LO.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof HPRE as P. unfold mdtor_pre in P.
destruct P as (RT & GSS & FLG & MTX & GD & [j1 S1] & [j2 S2]).
pose proof RT as RT'. destruct RT' as (PGC & GOT & GOT80 & REAL & SHB & INI & CANP & THR & RGL).
unfold MDTOR_W in RW.
repeat lazymatch type of RW with Forall _ (_ :: _) =>
let H := fresh "RW" in pose proof (Forall_inv RW) as H; cbn [fst snd] in H; apply Forall_inv_tail in RW end.
lit_rng.
pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp); (0x9ee80, 0x9ee88); (0x9fdf0, 0x9fdf8);
(0x7fffc1cc, 0x7fffc40c); (0x8000bc38, 0x8000bdd0)]%Z m) as MU.
pose proof (wmono_refl bsegs m) as WM.
Local Ltac2 Set LiaHints.tbl := fun () => "02M0?10088628586.12110188553603.87 10685224615.89 13000380547.11813000380547.89 13092900324.86 13169897334.1121371286659.115 1371286659.86  14201179716.79 14224430925.10814386403300.86 14386403301.11614980397443.11714980397443.87 15949657818.94 18265732580.11418265732580.84 18618292611.12318618292611.91 19006120615.84 19066511015.89 19208070823.87 1933448932.115 1933448932.86  20433961190.74 20805123751.87 21207973122.10821541434755.11621541434755.87 22193440237.10722519161511.87 23259527847.86 24708430881.98 25435258127.11525435258127.85 25566553219.11425566553219.84 25785063811.11725785063811.87 27192454931.79 27439898422.98 27442097076.81 2749330817.121 27681188262.77 28913119921.12128947464871.88 29371901571.10329371901571.89 29737833181.12130059936150.11230090674789.10230090674794.88 30189236903.91 30995698343.87 31399093385.10533510003693.10633971183717.87 33971183723.11834894844291.10234894844291.87 36574674563.11936574674563.88 36606830211.11936606830211.89 37238554472.90 37245778797.10837247578328.77 37247578331.79 37247661040.10837247661040.79 37504724647.91 378738307.87   3830064277.106 39242478692.86 3938769889.122 3940867048.90  39941648665.10740046219415.71 40158618216.12140540307045.87 40540307050.11741117850981.87 41117850986.11743061379371.72 43122952810.88 43122952811.11843507384707.11643507384707.87 44420783207.11344420783207.83 44964803431.11244964803431.80 46390321508.86 46392837507.11746392837507.87 47016595062.11447688149866.11747688149866.88 47900152984.94 49345969283.87 50269882218.11750269882218.88 51567446375.11451567446375.85 51693436583.87 52076332701.119523937423.94   53371277099.94 53510313876.1165368629927.88  54024088963.87 54140369575.87 54164510851.11354164510851.81 54509322919.87 55606215043.11655606215043.87 56170414366.94 56964914855.89 57387588263.87 57766271107.91 57915518083.11857915518083.88 58135773316.75 59178106163.85 59588178609.12160489146820.77 61262187744.77 61262187747.79 61592356519.88 62549928615.87 63507301651.80 63519175063.80 639945956.115  639945956.86   65508437732.10165508437732.86 65530800136.10865567805059.11865567805059.88 6615494311.89  66721159227.84 66772627111.87 66806001892.86 67081926311.81 67136312999.87 67157832433.12168094715463.77 7238556388.115 7238556388.86  7786772964.86  7786772965.116 9080374244.86  9080374245.116 9791719555.118 9791719555.89  00000100200300400500600700800900:00;00<00=00>00?00@00A00B00C00D00E00F00G00H00I00J00K00L00M00N00O00P00Q00R00S00T00U00V00W00X00Y00g01301401801901:01;01<01=01>01?01@01A01B01C01D01E01F01G01H01I01J01K01L01M01N01O01P01Q01R01S01T01X01Y01Z01[01_01c01d01e01f01g01h01l01m01n01o02002102202302402502602702802902:02>02?02@02A02B02C02D02E02F02G02H02I02J02K02L02M02N02O02P02Q02R02S02T02U02V02Z02[02\02]02^02_02`02a02b02c02d02e02f02g02k02l02m02n03903:03;03<03=03>03?03@03A03B03C03D03E03F03GSSSSSSSSSSFSSSSSSSSSSSSSSSSFSSSSSFSSSSSSFS2LO3KH'3RSP1HS2LO3KH'3RSPFS2LOSSSSFSSSSSSSSSSSSSSSSFFFFFSSS2LOSSSS2LOS2LOSSSSSS2LOSSSSSSSSSSSSSSS2LOSSSSSSFSSSSSSSSSSSSSSSSSS2LOSSFFFSSSSSSSSS2LOSSSS2LO3KH'2H3SSSSSSSSSSSSSS".
assert (RSF : rng RNG (bv_unsigned sp + -272) 272) by (eapply rng_sub'; [exact RSTK | lia]). move RIMG at bottom.
sort_lits. move S1 at top. move S2 at top.
carve_frame 16%nat ST.
do 9 hstep.
carve_frame 16%nat ST.
do 3 hstep. astep. hstep. hstep. astep. do 2 hstep. astep. do 4 hstep.
carve_frame 176%nat ST.
do 14 hstep.
do 5 hstep.
replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (vm_compute; reflexivity).
astep.
steps_to 0x40278%Z.
amo_step. astep. amo_step. astep. astep.
move MTX after RGL.
hstep. hstep. astep.
steps_to 0x4038c%Z.
lazymatch goal with M : munch _ m ?mc, W : wmono _ m ?mc |- _ =>
assert (GD' : gdescs mc 0x9e1c0 AGLOBALS)
by (eapply gdescs_transport; [exact GD| exact M| exact W| rewrite AGLOBALS_length; intros A n H1 H2 H3; cbn [disjoint_from]; lia]) end.
assert (HS : gshads _ AGLOBALS) by (eapply (gshads_of_hull AGLOBALS 0x7fffc1cc 0x7fffc40c); [exact S1| lia| lia| exact AGLOBALS_sorted]).
replace (Z_to_bv 64 51) with (Z_to_bv 64 (Z.of_nat (length AGLOBALS))) by reflexivity.
move RW2 at bottom.
call (unreg_loop AGLOBALS RNG 0x7fffc1cc 0x7fffc40c 0x9e1c0).
all: first [ unfold AGLOBALS; discriminate | exact GD' | exact HS | exact AGLOBALS_sorted | rewrite AGLOBALS_length; lia | side RIMG RSTK KH ].
clear RW2 GD GD' HS.
rewrite AGLOBALS_length.
do 6 hstep. hstep.
move RW3 at bottom.
call_sp (poison_low_spec RNG 0x8000bc38 408). all: side RIMG RSTK KH. clear RW3.
lit_nat.
steps_to 0x405e8%Z.
amo_step. astep. amo_step. astep. astep.
astep.
steps_to 0x40840%Z.
match goal with H : rw_cells _ _ (bv_unsigned sp + -208) _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp + -32) end.
hstep. hstep. hstep. hstep.
match goal with H : rw_cells _ _ (bv_unsigned sp + -32) _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp + -16) end.
hstep. hstep. hstep.
match goal with H : rw_cells _ _ (bv_unsigned sp + -16) _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp) end.
hstep.
unfold module_dtor_post. sys_finish.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section Closed.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Hypothesis get_set : forall s so, get_so (set_so so s) = so.
Hypothesis set_set : forall s so so', set_so so' (set_so so s) = set_so so' s.
Hypothesis set_get : forall s, set_so (get_so s) s = s.
Definition aexit_spec_closed :=
aexit_spec get_so set_so mdtor_pre module_dtor_proof mdtor_pre_frame
(F_stdio_exit.stdio_exit_proof get_so set_so get_set set_set set_get).
End Closed.
End CANSEC3.