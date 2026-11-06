(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg AProto ABase F_memset.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import AKit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import F_apoison.
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
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma poison_core0 : forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) fc (m m1 : amem) (addr size v lo : Z) (junk fj : list byte),
stk bsegs m1 lo (bv_unsigned sp + -64) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
mem_inv bsegs m1 ->
poison_cells m1 ->
rw_cells bsegs m1 (bv_unsigned sp + -64) [CB 8 fj; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
munch [(bv_unsigned sp - 64, bv_unsigned sp); (shad addr, shad addr + shlen size)]%Z m m1 -> wmono bsegs m m1 ->
addr mod 8 = 0 -> size mod 8 = 0 -> 0 <= size -> ablk (addr - 8) (addr + size) -> addr + size < 2^47 ->
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
pose proof HI as HI'. unfold ablk, AIMG_HI, KLS in HI'.
assert (SHR : 0x800b6e00 <= shad addr /\ shad addr + shlen size <= 0x10007fff8000 /\ 0 <= shlen size).
{ unfold shad, shlen, ASHOFF. Local Ltac2 Set LiaHints.tbl := fun () => "02S0?11801259171.10011801259171.10111801259171.92 11801259171.93 12367362435.81 12367362435.82 12367362435.89 12367362435.90 17776320417.90 17776320417.91 17776320430.81 17776320430.82 19618399904.86 19618399904.94 20970059894.80 20970059894.81 20970059894.89 20970059894.90 21918414723.82 21918414723.83 21918414723.91 21918414723.92 24982578106.71 24982578106.76 24982578737.69 25878270240.91 25878270240.92 25878270254.81 25878270254.82 26072764852.80 26072764853.79 26072764854.78 26074863037.72 26074863037.77 26082619953.79 26082619966.90 27056752999.81 28913119922.81 29429928528.10029429928528.10129429928528.92 29429928528.93 29442626420.73 29442626420.81 29784412410.74 29784412410.82 29784412664.73 29784412664.81 29784417117.69 29784418006.71 29784418006.76 29784418133.72 29786514268.80 29786562375.67 29788590300.10029788590300.10129788590300.92 29788590300.93 29794353372.86 29794353372.94 33434998178.10033434998178.10836115622433.90 36115622433.91 36115622446.81 36115622446.82 36423573305.10236423573305.10336423573305.94 36423573305.95 36993589379.82 36993589379.83 36993589379.91 36993589379.92 3945979267.81  3945979267.82  3945979267.88  3945979267.89  41809558659.80 41809558659.81 41809558659.90 41809558659.91 42501437472.86 42501437472.94 42501437473.85 42501437479.95 42503534624.72 42511603750.72 42511603879.71 42511604004.74 42511604133.73 42511604512.70 42511605419.75 43060403331.82 43060403331.83 43060403331.92 43060403331.93 43987951392.91 43987951392.92 43987951406.81 43987951406.82 44483185911.10144483185911.10244483185911.93 44483185911.94 44952393417.10044952393417.10144952393417.92 44952393417.93 49343888933.10249343888933.10349343888933.94 49343888933.95 51481786499.82 51481786499.83 51481786499.92 51481786499.93 52076332701.80 53767577772.87 53767577772.88 53767577775.80 53767577775.81 55750620234.74 55750620234.82 5637710115.120 5637710115.121 5637710115.128 5637710115.129 5637710124.102 5637710124.103 5637710124.94  5637710124.95  56777289877.12056777289877.12156777289877.12856777289877.12956777289882.10256777289882.10356777289882.94 56777289882.95 59308628566.71 59308628695.72 59308628820.73 59308628949.74 59308629082.75 59308629336.72 59308629336.77 59308632823.74 59308632823.82 59310725456.79 59310725457.80 59310725459.78 59588178610.81 61917199023.80 61917199023.81 61917199023.88 61917199023.89 63235321900.79 63235321900.80 63235321902.89 63235321902.90 65096534934.87 65098632080.78 00000?00N00]00l00m00n00o01001401801<01@01A01B01C01D01E01F01G01H01I01J01K01L01M01Q01U01Y01]01d01k02202H02R02h02o03G03H03K03N03Q03T03W03Z03[03\03]03^03_03`03a03b03c03d03e03f03g03h03i03j04R05=05A05E05I05M05Q05U05Y05]05^05_05`05a05b05c05d05e05f05g05h05i06606=06J06Q06]06d06n07507<07H07O07P07Q07R07S07W07[07_07c07o08;08G08S08V08Y08\08_08`08a08b08c08d08e08f08g08h08l09009409809=09B09G09L09Q09V09[09`09e09j09o0:70:<0:D0:I0:Q0:V0:^0:h0;20;B0;I0;P0;`0;j0<20<:0<B0<Y0<a0<b0<f0<j0<n0=20=60=:0=>0=B0=L0=YS4CEIL2LO1H3SHRS4CEIL2LO1H3SHRS4CEIL2LO1H3SHRS4CEIL2LO1H3SHRSSSSS2LOS2LOS2LOS2LOFFSSSSSSSSSSSS2LOS2LOS2LOS2LOS2HE2K9S2HE2K9S2HE2K9S2AL2SL2SZ2HE1V3HI'2K2S2SZ2HE2K7S2AL2SL2SZ2HE1V3HI'2K2S2HE2K9S2AL2SL2SZ1V1H3HI'2H02H5SS1VS1VS1VS1VS1VS1VSSSSSSSSSSSSSSSSS2AL2SL2SZ1V3HI'2K22H02H52H63H103H153H16S2AL2SL1V1H3HI'2K93K122H02H52H63H103H153H16S2LOS2LOS2LOS2LOS2LOS2LOS2LOS2LOSSSSSSSSSSSSS2SZ1V3HI'2K2S2K22K3S2SZ1V3HI'2K2S2K22K3S2SZ1V1H3HI'S2K22K3S2SZ2HE2K2S2K22K3S2K22K3S2SZ1V1H3HI'S2K22K3SSSSS2LOS2LOS2LOS2LOS4CEIL1H3SHRS4CEIL1H3SHRS4CEIL1H3SHRS4CEIL1H3SHRS1VS1VS1VS1VSSSSSSSSFS2LOS2LOS2LOS2LOS3SHRS3SHRS3SHRS3SHRS3SHRS3SHRS3SHRS3SHRS3SHRS3SHRS3SHRS3SHR2KTS3SHRS3SHR2KTS3SHRS3SHR2KTS3SHRS3SHR2KTS2SZ2HE2K3S2SZ2HE2K4S2SZ1V3HI'2K22K5S2K42K6S2K52K7S2SZ1V3HI'2K22K9S2SZ2K72K9S3SHR2KTS3SHR2KTS2HE3K11S2AL2SL2SZ1V3HI'2K93K12S2HE3K10SS2LOS2LOS2LOS2LOS2LOS2LOS2LOS2LOS2SZ2HE2K7S2SZ1V3HI'2K2".
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
#[using="Type"] Lemma poison_shadow_spec0 : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (addr size v lo : Z) (junk : list byte),
stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
mem_inv bsegs m ->
poison_cells m ->
a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 v ->
addr mod 8 = 0 -> size mod 8 = 0 -> 0 <= size -> ablk (addr - 8) (addr + size) -> addr + size < 2^47 ->
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
assert (SHR : 0x800b6e00 <= shad addr /\ shad addr + shlen size <= 0x10007fff8000 /\ 0 <= shlen size).
{ unfold shad, shlen, ASHOFF. Local Ltac2 Set LiaHints.tbl := fun () => "01W0>10521085166.7610600373102.7811041912942.7811912744615.7812367362435.7812685940462.7613021749692.781527479463.76 16354687726.7917646078182.6917776320431.771792056942.78 17939878638.791892362350.78 19049469500.7819622476014.7921918414723.7823036111982.7823483264238.7624630998586.7625071629079.7625071629079.7825071629079.7925167604974.7825314760359.7825792608750.7925878270255.7726961506542.7927056752999.7927335527918.7827908601838.7929442626420.7129531591534.7829786562375.6529870281326.7831081687356.7931466597614.7632651489978.7832716547054.7833039531175.7933486665994.7933680001082.7934056952330.7935262033390.7835310472686.7836115622446.7836204177774.783640025710.78 36993589379.7937107179452.7837124862062.7838889585390.793945979267.78 39849574766.7840059657198.7841072247790.7841809558659.7643060403331.7943061431595.6743987951406.7844253452910.7844750652170.7845221239098.7846923716878.7147178742894.7848490912238.7948593432558.7948923332334.7651014030958.7951481786499.785363218414.79 53767577775.7754324225646.7855067441390.7955735955265.7156007886318.7856066145674.7856228262055.78563227834.78  57745675194.7858732652910.7859391397898.7659445487498.7860025031335.7961104133998.7961917199023.7762019383790.7962309656174.7862473508590.7663235321900.7563239821294.7863694018620.7965262970532.7165782973294.7866761942666.7867800801447.7868044863854.767010956092.76 7260965451.71 8583720762.79 9193927790.78 985337532.78  992066670.78  00000;00F00Q00R00S00^00b00c00n00o01301>01I01T01X01c01d01o02:02?02@02A02B02M02N02Y02]02h03@03K03V03Y03d03e04004404?04D04O04P04_04d05305>05I05M05X05c05d05h06306>06?06J06U06`06a06b06f06j07507D07I07N07Y07d07o08:08E08F08Q08U08`08k08l09709F09G09L09Q09\09k0::0:;0:F0:J0:U0:`0:k0:o0;:0;>0;?0;J0;Y0;Z0;e0;i0<40<90<D0<H0<SS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HSSS4CEIL2LO1HS2HBSS4CEIL2LO1HSS2LOS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS2HBS4CEIL2LO1HSS4CEIL2LO1HS4CEIL2LO1HS3SPRSSSS4CEIL2LO1HSS4CEIL2LO1HS2LOS4CEIL2LO1HS2AL2SL2SZ1V1H3HI'2H02H5S4CEIL2LO1HS4CEIL2LO1HS1VS4CEIL2LO1HSS4CEIL2LO1HS2HBS4CEIL2LO1HS3SPRS4CEIL2LO1HSS4CEIL2LO1H3SHRS3SPRS4CEIL2LO1H3SHRS4CEIL2LO1HS4CEIL2LO1HS2LOS4CEIL2LO1HS4CEIL2LO1HSS2HBS4CEIL2LO1HS4CEIL2LO1HSS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HSSS2LOS2LOS4CEIL2LO1HS4CEIL2LO1H3SHRS3SPRS3SHRS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HSS4CEIL2LO1HS2LOS4CEIL2LO1HS4CEIL2LO1HFS4CEIL2LO1HS4CEIL2LO1H3SHRSS3SPRS3SPRS4CEIL2LO1HS4CEIL2LO1H3SHRS4CEIL2LO1H3SHRSS4CEIL2LO1HS2LOS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS2LOS4CEIL2LO1HS2HBSS4CEIL2LO1HS4CEIL2LO1H3SHRSS4CEIL2LO1HS2HBS4CEIL2LO1HS3SPRS4CEIL2LO1HS2HBS4CEIL2LO1H".
rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
word_range sp SPR.
carve_frame 64%nat ST.
do 8 step.
step. if_cases KV; zify_cond KV.
2: step; lstep; step; step; if_lit.
all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
eapply (poison_core0 RNG ra sp gp tp t0 t1 t2 s0 s1 _ _ _ a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mm addr size v lo junk) end.
all: try eassumption; try lia.
all: eapply poison_cells_frame; [exact PC | exact MU | exact WM | ].
all: apply Forall_cons; [cbn; unfold AIMG_HI; lia|]; apply Forall_cons; [cbn; unfold AIMG_HI; lia | apply Forall_nil].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition poison_post_k (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(addr k v lo : Z) (m : amem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (shad addr, shad addr + k)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp)
/\ rw_cells bsegs m' (shad addr) [CB (Z.to_nat k) (repeat (Z_to_bv 8 v) (Z.to_nat k))].
#[using="Type"] Lemma poison_shadow_spec_k : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (addr size k v lo : Z) (junk : list byte),
stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
mem_inv bsegs m ->
poison_cells m ->
a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 v ->
addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> ablk addr (addr + size) -> addr + size <= 2^47 ->
0 <= v < 256 -> (v = 0 -> shlen size < 0xffffffffffffffff) -> shlen size = k ->
rw_cells bsegs m (shad addr) [CB (Z.to_nat k) junk] ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad addr) k ->
evtF bsegs RNG (poison_post_k ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr k v lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x54060) fc None m (seg_rom bsegs)).
Proof.
intros until junk. intros ST CEIL LO MI PC Ha0 Ha1 Ha2 AL SL SZ HI HE V V0 HK DST RIMG RSTK RSH. subst k.
unfold poison_post_k. eapply poison_shadow_spec; eassumption.
Qed.
#[using="Type"] Lemma poison_shadow_spec0_k : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (addr size k v lo : Z) (junk : list byte),
stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
mem_inv bsegs m ->
poison_cells m ->
a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 v ->
addr mod 8 = 0 -> size mod 8 = 0 -> 0 <= size -> ablk (addr - 8) (addr + size) -> addr + size < 2^47 ->
0 <= v < 256 -> (v = 0 -> shlen size < 0xffffffffffffffff) -> shlen size = k ->
rw_cells bsegs m (shad addr) [CB (Z.to_nat k) junk] ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad addr) k ->
evtF bsegs RNG (poison_post_k ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr k v lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x54060) fc None m (seg_rom bsegs)).
Proof.
intros until junk. intros ST CEIL LO MI PC Ha0 Ha1 Ha2 AL SL SZ HI HE V V0 HK DST RIMG RSTK RSH. subst k.
unfold poison_post_k. eapply poison_shadow_spec0; eassumption.
Qed.
End CANSEC1.
