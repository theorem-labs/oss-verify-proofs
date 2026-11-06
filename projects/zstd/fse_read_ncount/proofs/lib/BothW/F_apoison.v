(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg AProto ABase F_memset.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import AKit.
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

Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
Definition poison_cells (m : amem) : Prop :=
rw_cells bsegs m 0x99900 [C8 (Z_to_bv 64 0x134068); C8 (Z_to_bv 64 0x9fd38); C8 (Z_to_bv 64 0xa2538);
C8 (Z_to_bv 64 0xa3228); C8 (Z_to_bv 64 0xa3230); C8 (Z_to_bv 64 0xa3220)]
/\ rw_cells bsegs m 0x99930 [C8 (Z_to_bv 64 0x9b778)]
/\ rw_cells bsegs m 0x9b770 [C8 (Z_to_bv 64 0x92c40); C8 (Z_to_bv 64 0x93044)]
/\ rw_cells bsegs m 0xa2538 [C8 (Z_to_bv 64 0x7fff8000)]
/\ rw_cells bsegs m 0xa3220 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
/\ rw_cells bsegs m 0xa1d9c [C1 (Z_to_bv 8 1)]
/\ rw_cells bsegs m 0x1340e0 [C8 (Z_to_bv 64 0xffffffffffffffff)].
#[using="Type"] Lemma poison_cells_frame : forall m m' W,
poison_cells m -> munch W m m' -> wmono bsegs m m' ->
Forall (fun iv => AIMG_HI <= fst iv) W -> poison_cells m'.
Proof.
intros m m' W PC MU WM HW.
assert (D : forall A n, A + n <= AIMG_HI -> disjoint_from W A n).
{ intros A n HA. clear MU. induction HW as [|[lo hi] W H1 H2 IH]; cbn in *; [exact I|]. split; [lia| exact IH]. }
unfold poison_cells, AIMG_HI in *.
destruct PC as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
repeat split; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply D; cbn; lia]).
Qed.
Definition poison_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(addr size v lo : Z) (m : amem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (shad addr, shad addr + shlen size)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp)
/\ rw_cells bsegs m' (shad addr) [CB (Z.to_nat (shlen size)) (repeat (Z_to_bv 8 v) (Z.to_nat (shlen size)))].
End CANSEC1.
Local Ltac poison_tail sp v MU WM DST RSH FR ST :=
do 3 step; do 8 step; step;
eapply evtF_mono;
[ eapply memset_spec;
[ rewrite !unsigned_lit by (unfold shlen in *; rewrite ?Z.shiftr_div_pow2 in * by lia; Z.div_mod_to_equations; lia); exact DST
| assumption
| rewrite !unsigned_lit by (unfold shlen in *; rewrite ?Z.shiftr_div_pow2 in * by lia; Z.div_mod_to_equations; lia); exact RSH ]
| ];
let ms' := fresh "ms'" in let PO := fresh "PO" in let MU2 := fresh "MU2" in let WM2 := fresh "WM2" in
let MI2 := fresh "MI2" in let DST2 := fresh "DST2" in let FR' := fresh "FR'" in let ST' := fresh "ST'" in
intros ms' PO; unfold memset_post in PO; unfold poison_post; destruct_exs PO;
destruct PO as (-> & MU2 & WM2 & MI2 & DST2);
rewrite !unsigned_lit in MU2, DST2 by (unfold shlen in *; rewrite ?Z.shiftr_div_pow2 in * by lia; Z.div_mod_to_equations; lia);
rewrite ?unsigned_lit in DST2 by lia; rewrite ?(Z.mod_small v 256) in DST2 by lia; change (0 mod 256) with 0 in DST2;
do 16 eexists; split; [reflexivity|];
split; [eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MU2]; let xq := fresh in let Hxq := fresh in intros xq Hxq; cbn in Hxq |- *; tauto |];
split; [eapply wmono_trans; [exact WM| exact WM2] |]; split; [exact MI2|];
split; [| exact DST2];
pose proof (rw_cells_transport bsegs _ _ _ _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize]; lia)) as FR';
pose proof (stk_transport_disjoint bsegs _ _ _ _ _ ST MU2 WM2 ltac:(cbn [disjoint_from]; lia)) as ST';
eapply stk_release in FR'; [| exact ST' | lia]; cbn [cells_size csize Nat.add] in FR';
match type of FR' with stk _ _ _ ?hi => replace hi with (bv_unsigned sp) in FR' by lia end; exact FR'.
Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Lemma poison_core : forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) fc (m m1 : amem) (addr size v lo : Z) (junk fj : list byte),
stk bsegs m1 lo (bv_unsigned sp + -64) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
mem_inv bsegs m1 ->
poison_cells m1 ->
rw_cells bsegs m1 (bv_unsigned sp + -64) [CB 8 fj; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
munch [(bv_unsigned sp - 64, bv_unsigned sp); (shad addr, shad addr + shlen size)]%Z m m1 -> wmono bsegs m m1 ->
addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> ablk addr (addr + size) -> addr + size <= 2^47 ->
0 <= v < 256 -> (v = 0 -> shlen size < 0xffffffffffffffff) ->
rw_cells bsegs m1 (shad addr) [CB (Z.to_nat (shlen size)) junk] ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad addr) (shlen size) ->
evtF bsegs RNG (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size v lo m)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 addr) (Z_to_bv 64 size) (Z_to_bv 64 v) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x54094) fc None m1 (seg_rom bsegs)).
Proof.
intros until fj. intros ST CEIL LO MI PC FR MU WM AL SL SZ HI HE V V0 DST RIMG RSTK RSH.
atop_facts. destruct PC as (GOT & GOTMS & REAL & SHB & LAY & CANP & THR).
unfold ablk, AIMG_HI, KLS in HI.
assert (SHR : 0x800b6e00 <= shad addr /\ shad addr + shlen size <= 0x10007fff8000 /\ 0 < shlen size).
{ unfold shad, shlen, ASHOFF. Local Ltac2 Set LiaHints.tbl := fun () => "02S0?11801259171.10011801259171.91 11801259171.92 11801259171.99 12367362435.80 12367362435.81 12367362435.88 12367362435.89 17776320417.89 17776320417.90 17776320430.80 17776320430.81 19618399904.85 19618399904.93 20970059894.79 20970059894.80 20970059894.88 20970059894.89 21918414723.81 21918414723.82 21918414723.90 21918414723.91 24982578106.70 24982578106.75 24982578737.68 25878270240.90 25878270240.91 25878270254.80 25878270254.81 26072764852.79 26072764853.78 26072764854.77 26074863037.71 26074863037.76 26082619953.78 26082619966.89 27056752999.80 28913119922.80 29429928528.10029429928528.91 29429928528.92 29429928528.99 29442626420.72 29442626420.80 29782367974.66 29784412410.73 29784412410.81 29784412664.72 29784412664.80 29784417117.68 29784418006.70 29784418006.75 29784418133.71 29786514268.79 29788590300.10029788590300.91 29788590300.92 29788590300.99 29794353372.85 29794353372.93 33434998178.10733434998178.99 36115622433.89 36115622433.90 36115622446.80 36115622446.81 36423573305.10136423573305.10236423573305.93 36423573305.94 36993589379.81 36993589379.82 36993589379.90 36993589379.91 3945979267.80  3945979267.81  3945979267.87  3945979267.88  41809558659.79 41809558659.80 41809558659.89 41809558659.90 42501437472.85 42501437472.93 42501437473.84 42501437479.94 42503534624.71 42511603750.71 42511603879.70 42511604004.73 42511604133.72 42511604512.69 42511605419.74 43060403331.81 43060403331.82 43060403331.91 43060403331.92 43987951392.90 43987951392.91 43987951406.80 43987951406.81 44483185911.10044483185911.10144483185911.92 44483185911.93 44952393417.10044952393417.91 44952393417.92 44952393417.99 49343888933.10149343888933.10249343888933.93 49343888933.94 51481786499.81 51481786499.82 51481786499.91 51481786499.92 52076332701.79 53767577772.86 53767577772.87 53767577775.79 53767577775.80 55750620234.73 55750620234.81 5637710115.119 5637710115.120 5637710115.127 5637710115.128 5637710124.101 5637710124.102 5637710124.93  5637710124.94  56777289877.11956777289877.12056777289877.12756777289877.12856777289882.10156777289882.10256777289882.93 56777289882.94 59308628566.70 59308628695.71 59308628820.72 59308628949.73 59308629082.74 59308629336.71 59308629336.76 59308632823.73 59308632823.81 59310725456.78 59310725457.79 59310725459.77 59588178610.80 61917199023.79 61917199023.80 61917199023.87 61917199023.88 63235321900.78 63235321900.79 63235321902.88 63235321902.89 65096534934.86 65098632080.77 00000?00N00]00l00m00n00o01001401801<01@01A01B01C01D01E01F01G01H01I01J01K01L01M01Q01U01Y01]01d01k02202G02Q02f02m03D03E03H03K03N03Q03T03W03X03Y03Z03[03\03]03^03_03`03a03b03c03d03e03f03g04Q05805<05@05D05H05L05P05T05X05Y05Z05[05\05]05^05_05`05a05b05c05d05m06406=06D06R06Y06c06j07107?07F07G07H07I07J07N07R07V07Z07f08208>08J08M08P08S08V08W08X08Y08Z08[08\08]08^08_08c08g08k08o09409909>09C09H09M09R09W09\09a09f09n0:30:;0:@0:H0:M0:U0:_0:i0;;0;B0;I0;U0;_0;g0;o0<70<K0<S0<T0<X0<\0<`0<d0<h0<l0=00=40=>0=JS4CEIL2LO1H3SHRS4CEIL2LO1H3SHRS4CEIL2LO1H3SHRS4CEIL2LO1H3SHRSSSSS2LOS2LOS2LOS2LOFFSSSSSSSSSSSS2LOS2LOS2LOS2LOS2HE2K9S2HE2K9S2HE2K9S2AL2SL2SZ2HI2HE1V2K2S2SZ2HE2K7S2AL2SL2SZ2HI2HE1V2K2S2HE2K9S2AL2SL2SZ2HI1V1H2H02H5SS1VS1VS1VS1VS1VS1VSSSSSSSSSSSSSSSSS2AL2SL2HI1V1H2K93K122H02H52H63H103H153H16S2AL2SL2SZ2HI1V2K22H02H52H63H103H153H16S2LOS2LOS2LOS2LOS2LOS2LOS2LOS2LOSSSSSSSSSSSSS2HI1V2K2S2K22K3S2HI1V2K2S2K22K3S2SL2SZ2HI1V1HS2K22K3S2SZ2HE2K2S2K22K3S2K22K3S2SL2SZ2HI1V1HS2K22K3SSSSS2LOS2LOS2LOS2LOS4CEIL1H3SHRS4CEIL1H3SHRS4CEIL1H3SHRS4CEIL1H3SHRS1VS1VS1VS1VSSSSSSSSFS2LOS2LOS2LOS2LOS3SHRS3SHRS3SHRS3SHRS3SHRS3SHRS3SHRS3SHRS3SHRS3SHRS3SHRS3SHR2KTS3SHRS3SHR2KTS3SHRS3SHR2KTS3SHRS3SHR2KTS2SZ2HE2K3S2SZ2HE2K4S2SL2SZ2HI1V2K22K5S2K42K6S2K52K7S2HI1V2K22K9S2SZ2K72K9S3SHR2KTS3SHR2KTS2HE3K11S2AL2SL2SZ2K22K73K12S2HE3K10SS2LOS2LOS2LOS2LOS2LOS2LOS2LOS2LOS2SZ2HE2K7S2SZ2HI1V2K2".
rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
zstep. step. if_cases K1; zify_cond K1.
{ exfalso. apply K1. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact AL. }
do 3 step.
do 4 zstep.
match goal with |- context [Z.land ?x 2147450879] => let v := eval vm_compute in (Z.land x 2147450879) in change (Z.land x 2147450879) with v end.
step. if_cases K2; zify_cond K2.
2: do 6 step.
2: zstep; step; if_cases K3; zify_cond K3; [| exfalso; lia].
2: do 3 step; do 2 zstep.
2: step; if_cases K4; zify_cond K4; [exfalso; lia|].
2: step; if_cases K5; zify_cond K5; [| exfalso; lia].
2: step; do 2 zstep.
2: step; if_cases K6; zify_cond K6; [exfalso; lia|].
2: step; if_cases K7; zify_cond K7; [| exfalso; lia].
all: zstep; step; if_cases K8; zify_cond K8;
[ exfalso; apply K8; change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; exact SL |].
all: do 2 zstep.
all: step; if_cases K9; zify_cond K9.
all: try (exfalso; lia).
2: do 6 step; zstep.
2: step; if_cases K10; zify_cond K10; [| exfalso; lia].
2: do 3 step; do 2 zstep.
2: step; if_cases K11; zify_cond K11; [exfalso; lia|].
2: step; if_cases K12; zify_cond K12; [exfalso; lia|].
all: do 3 step.
all: step; if_lit.
all: do 5 zstep.
all: replace ((Z.shiftr (addr + size + -8) 3 + 1) mod 18446744073709551616 - Z.shiftr addr 3) with (shlen size)
by (unfold shlen; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
all: change (2147450880 + Z.shiftr addr 3) with (shad addr).
all: step; if_cases KV; zify_cond KV;
[| do 2 step; lstep; step; if_cases KT; zify_cond KT;
[| exfalso; rewrite ?Z.mod_small in KT by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia); lia]].
all: poison_tail sp v MU WM DST RSH FR ST.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma poison_shadow_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (addr size v lo : Z) (junk : list byte),
stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
mem_inv bsegs m ->
poison_cells m ->
a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 v ->
addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> ablk addr (addr + size) -> addr + size <= 2^47 ->
0 <= v < 256 -> (v = 0 -> shlen size < 0xffffffffffffffff) ->
rw_cells bsegs m (shad addr) [CB (Z.to_nat (shlen size)) junk] ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad addr) (shlen size) ->
evtF bsegs RNG (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size v lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x54060) fc None m (seg_rom bsegs)).
Proof.
intros until junk. intros ST CEIL LO MI PC -> -> -> AL SL SZ HI HE V V0 DST RIMG RSTK RSH.
atop_facts. pose proof PC as PC'. destruct PC' as (GOT & GOTMS & REAL & SHB & LAY & CANP & THR).
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (shad addr, shad addr + shlen size)]%Z m) as MU.
pose proof (wmono_refl bsegs m) as WM.
pose proof HI as HI'. unfold ablk, AIMG_HI, KLS in HI'.
assert (SHR : 0x800b6e00 <= shad addr /\ shad addr + shlen size <= 0x10007fff8000 /\ 0 < shlen size).
{ unfold shad, shlen, ASHOFF. Local Ltac2 Set LiaHints.tbl := fun () => "01W0>10521085166.7610600373102.7811041912942.7811912744615.7812367362435.7812685940462.7613021749692.781527479463.76 16354687726.7917646078182.6917776320431.771792056942.78 17939878638.791892362350.78 19049469500.7819622476014.7921918414723.7823036111982.7823483264238.7624630998586.7625071629079.7625071629079.7825071629079.7925167604974.7825314760359.7825792608750.7925878270255.7726961506542.7927056752999.7927335527918.7827908601838.7929442626420.7129531591534.7829786562375.6529870281326.7831081687356.7931466597614.7632651489978.7832716547054.7833039531175.7933486665994.7933680001082.7934056952330.7935262033390.7835310472686.7836115622446.7836204177774.783640025710.78 36993589379.7937107179452.7837124862062.7838889585390.793945979267.78 39849574766.7840059657198.7841072247790.7841809558659.7643060403331.7943061431595.6743987951406.7844253452910.7844750652170.7845221239098.7846923716878.7147178742894.7848490912238.7948593432558.7948923332334.7651014030958.7951481786499.785363218414.79 53767577775.7754324225646.7855067441390.7955735955265.7156007886318.7856066145674.7856228262055.78563227834.78  57745675194.7858732652910.7859391397898.7659445487498.7860025031335.7961104133998.7961917199023.7762019383790.7962309656174.7862473508590.7663235321900.7563239821294.7863694018620.7965262970532.7165782973294.7866761942666.7867800801447.7868044863854.767010956092.76 7260965451.71 8583720762.79 9193927790.78 985337532.78  992066670.78  00000;00F00Q00R00S00^00b00c00n00o01301>01I01T01X01c01d01o02:02?02@02A02B02M02N02Y02]02h03@03K03V03Y03d03e04004404?04D04O04P04_04d05305>05I05M05X05c05d05h06306>06?06J06U06`06a06b06f06j07507D07I07N07Y07d07o08:08E08F08Q08U08`08k08l09709F09G09L09Q09\09k0::0:;0:F0:J0:U0:`0:k0:o0;:0;>0;?0;J0;Y0;Z0;e0;i0<40<90<D0<H0<SS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HSSS4CEIL2LO1HS2HBSS4CEIL2LO1HSS2LOS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS2HBS4CEIL2LO1HSS4CEIL2LO1HS4CEIL2LO1HS3SPRSSSS4CEIL2LO1HSS4CEIL2LO1HS2LOS4CEIL2LO1HS2AL2SL2SZ1V1H3HI'2H02H5S4CEIL2LO1HS4CEIL2LO1HS1VS4CEIL2LO1HSS4CEIL2LO1HS2HBS4CEIL2LO1HS3SPRS4CEIL2LO1HSS4CEIL2LO1H3SHRS3SPRS4CEIL2LO1H3SHRS4CEIL2LO1HS4CEIL2LO1HS2LOS4CEIL2LO1HS4CEIL2LO1HSS2HBS4CEIL2LO1HS4CEIL2LO1HSS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HSSS2LOS2LOS4CEIL2LO1HS4CEIL2LO1H3SHRS3SPRS3SHRS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HSS4CEIL2LO1HS2LOS4CEIL2LO1HS4CEIL2LO1HFS4CEIL2LO1HS4CEIL2LO1H3SHRSS3SPRS3SPRS4CEIL2LO1HS4CEIL2LO1H3SHRS4CEIL2LO1H3SHRSS4CEIL2LO1HS2LOS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS2LOS4CEIL2LO1HS2HBSS4CEIL2LO1HS4CEIL2LO1H3SHRSS4CEIL2LO1HS2HBS4CEIL2LO1HS3SPRS4CEIL2LO1HS2HBS4CEIL2LO1H".
rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
word_range sp SPR.
carve_frame 64%nat ST.
do 8 step.
step. if_cases KV; zify_cond KV.
2: step; lstep; step; step; if_lit.
all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
eapply (poison_core RNG ra sp gp tp t0 t1 t2 s0 s1 _ _ _ a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mm addr size v lo junk) end.
all: try eassumption; try lia.
all: eapply poison_cells_frame; [exact PC | exact MU | exact WM | ].
all: apply Forall_cons; [cbn; unfold AIMG_HI; lia|]; apply Forall_cons; [cbn; unfold AIMG_HI; lia | apply Forall_nil].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC2.
