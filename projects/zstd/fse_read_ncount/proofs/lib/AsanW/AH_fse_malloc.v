(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Frame.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import DrvAgree Stdio_pure.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface AKit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
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

Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND, shlen in *; rewrite ?Z.shiftr_div_pow2 in * by lia.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Ltac retlit := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; rpc) end.
Section CANSEC1. Context {rc : runConstT}.
Definition AFUZZ_MALLOC : Z := 0x827d8.
Definition APROD_CREATE : Z := 0x82564.
Definition APROD_FREE : Z := 0x825e4.
Definition APCREATE_RET : Z := 0x82594.
Definition FUZZ_MALLOC_STACK_A : Z := 16 + AMALLOC_STACK.
Definition PROD_CREATE_STACK_A : Z := 32 + FUZZ_MALLOC_STACK_A.
Section Stmts.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Definition fuzz_mallocA_post (L : alayout) (RNG : footprint)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
(s : APS) (LB : list ablock) (n lo : Z) (m : amem)
(r : option AsanCtrl.aptr) (s' : APS) (RNG' : footprint) : machine_state -> Prop :=
fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (p : AsanCtrl.aptr) (A : Z) (junk : list byte),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
FR (ret_pc ra) fc None m' (seg_rom asegs)
/\ r = Some p
/\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ aheap_pres CI LB (bv_unsigned sp) m m'
/\ aps_rest s' = aps_rest s
/\ ablock_range A n
/\ AHEAP AI L RNG' (aps_m s') (HB p A n :: LB) m'
/\ rw_cells asegs m' A [CB (Z.to_nat n) junk]
/\ rng RNG' A n /\ rng RNG' (shad A) (shlen (n + 7)).
Definition fuzz_mallocA_stmt : Prop :=
forall (L : alayout) (RNG : footprint)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(FR : bvmap 5 word) (fc : bv 32) (m : amem)
(s : APS) (LB : list ablock) (n lo : Z),
AHEAP AI L RNG (aps_m s) LB m ->
mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - FUZZ_MALLOC_STACK_A ->
bv_unsigned sp < al_top L -> bv_unsigned sp mod 16 = 0 ->
tp = Z_to_bv 64 ATP ->
a0 = Z_to_bv 64 n -> 0 < n <= AREQMAX ->
In [AMALLOC_PC; AFMALLOC_RET] (al_U L) ->
rng RNG lo (al_top L - lo) -> rng_aimg RNG ->
aps_ok L s ->
implMA RNG (Harness.fuzz_malloc amalloc_M (new_handlerA AAllocAsan) n) s
(fuzz_mallocA_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc s LB n lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
FR (Z_to_bv 64 AFUZZ_MALLOC) fc None m (seg_rom asegs)).
Definition prod_createA_post (L : alayout) (RNG : footprint)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
(s : APS) (LB : list ablock) (lo : Z) (dataw sizew : word) (m : amem)
(r : option AsanCtrl.aptr) (s' : APS) (RNG' : footprint) : machine_state -> Prop :=
fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (p : AsanCtrl.aptr) (A : Z),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
FR (ret_pc ra) fc None m' (seg_rom asegs)
/\ r = Some p
/\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ aheap_pres CI LB (bv_unsigned sp) m m'
/\ aps_rest s' = aps_rest s
/\ ablock_range A PRODUCER_SIZE
/\ AHEAP AI L RNG' (aps_m s') (HB p A PRODUCER_SIZE :: LB) m'
/\ rw_cells asegs m' A [C8 dataw; C8 sizew]
/\ rng RNG' A PRODUCER_SIZE /\ rng RNG' (shad A) (shlen (PRODUCER_SIZE + 7)).
Definition prod_createA_stmt : Prop :=
forall (L : alayout) (RNG : footprint)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(FR : bvmap 5 word) (fc : bv 32) (m : amem)
(s : APS) (LB : list ablock) (lo : Z),
AHEAP AI L RNG (aps_m s) LB m ->
mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - PROD_CREATE_STACK_A ->
bv_unsigned sp < al_top L -> bv_unsigned sp mod 16 = 0 ->
tp = Z_to_bv 64 ATP ->
In [AMALLOC_PC; AFMALLOC_RET] (al_U L) ->
rng RNG lo (al_top L - lo) -> rng_aimg RNG ->
aps_ok L s ->
implMA RNG (Harness.fuzz_malloc amalloc_M (new_handlerA AAllocAsan) PRODUCER_SIZE) s
(prod_createA_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc s LB lo a0 a1 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
FR (Z_to_bv 64 APROD_CREATE) fc None m (seg_rom asegs)).
Definition prod_freeA_stmt_at (entry : Z) : Prop :=
forall (L : alayout) (RNG : footprint)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(FR : bvmap 5 word) (fc : bv 32) (m : amem)
(s : APS) (LB : list ablock) (p : AsanCtrl.aptr) (A n lo : Z) (tr : list Z),
AHEAP AI L RNG (aps_m s) LB m -> In (HB p A n) LB ->
mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
bv_unsigned sp + 16 < al_top L ->
tp = Z_to_bv 64 ATP ->
a0 = Z_to_bv 64 A ->
uchain m (al_top L) AFREE_PC (bv_unsigned sp) (bv_unsigned s0) UDEPTH tr ->
In (AFREE_PC :: bv_unsigned ra :: tr) (al_U L) ->
bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC -> (length tr <= 28)%nat ->
bv_unsigned sp mod 16 = 0 ->
rng RNG lo (al_top L - lo) ->
aps_ok L s ->
implMA RNG (afree_M p) s
(fun _ s' RNG' ms' => aps_rest s' = aps_rest s
/\ afree_post CI (AHEAP AI) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc (aps_m s) LB p lo m (aps_m s') RNG' ms')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
FR (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
#[using="Type"] Lemma aheap_pres_frame : forall L RNG st LB m m' W lo SP,
AHEAP AI L RNG st LB m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => lo <= fst iv /\ snd iv <= SP) W -> ATOP + 4096 <= lo -> SP <= al_top L ->
aheap_pres CI LB SP m m'.
Proof.
intros L RNG st LB m m' W lo SP AH MU WM FW BOT TOP.
pose proof (AI_layout AI _ _ _ _ _ AH) as (LAY1 & LAY2 & LAY3 & LAY4 & _).
eapply aheap_pres_of_munch; [exact MU| exact WM|]. intros a Hc.
pose proof (AI_aci_img AI) as CIB.
assert (HA : a < lo \/ SP <= a).
{ destruct Hc as [Hc|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]]; unfold AIMG_HI in *.
- Local Ltac2 Set LiaHints.tbl := fun () => "0070>24830919534.2524830919534.2824830919534.3031788166912.1237273198525.2546168014977.136494881682.28 00000300900B00L00P00a00nS1HS2Hr1HS2Hr1H2H0S2HA2F12F2S2HcS3BOT3A471H2H02H4S3BOT2Hr1H2H0".
right; lia.
- left. pose proof (CIB iv Hiv). unfold AIMG_HI in *. atop_facts. lia.
- left. pose proof (AI_block_bounds AI _ _ _ _ _ b AH Hb). unfold AIMG_HI in *. lia.
- left. rewrite shad_div. unfold ASHOFF.
assert (A47 : a' < 2^47).
{ destruct Ha' as [H|[(iv & Hiv & Hr)|(c & FA & fn & Hb & Hr)]]; [lia| pose proof (CIB iv Hiv); unfold AIMG_HI in *; lia|].
pose proof (AI_block_bounds AI _ _ _ _ _ _ AH Hb). cbn in *. atop_facts. lia. }
atop_facts. clear - A47 BOT. Z.div_mod_to_equations. lia. }
clear - HA FW. induction W as [|[wlo whi] W IH]; [exact I|]. cbn. inversion FW as [|x l [F1 F2] FW']; subst. cbn in F1, F2.
split; [lia| apply IH; exact FW'].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma aheap_pres_fresh : forall L RNG st LB m m' p A n lo SP,
AHEAP AI L RNG st (HB p A n :: LB) m -> munch [(A, A + n); (lo, SP)] m m' -> wmono asegs m m' ->
ATOP + 4096 <= lo -> lo <= SP -> SP <= 2^47 ->
aheap_pres CI LB SP m m'.
Proof.
intros L RNG st LB m m' p A n lo SP AH MU WM BOT LOSP TOP.
pose proof (AI_block AI _ _ _ _ _ p A n AH (or_introl eq_refl)) as (_ & (BR1 & BR2 & BR3 & BR4) & _).
pose proof (ablk_lin _ _ BR1) as (BL1 & BL2 & BL3 & BL4). unfold AIMG_HI in BL1.
pose proof (AI_blocks_nodup AI _ _ _ _ _ AH) as ND. inversion ND as [|x l NI ND']; subst.
pose proof (AI_aci_img AI) as CIB.
eapply aheap_pres_of_munch; [exact MU| exact WM|]. intros a Hc. cbn [outside].
destruct Hc as [Hc|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
- Local Ltac2 Set LiaHints.tbl := fun () => "00;0>15762232342.3415762232342.3915768528942.3740461571878.3440463674013.3840463674142.3958852435904.1465129518411.386739899560.37 6741985424.34 6741985424.39 00000400?00L00Q00Z00c01401801B01S01^S2HcS3BOT2Hr2BBS3BOT2Hr1H2H0S1X1HS2Hr1H2H0S2Hr1H2H0S3BOT3A471H2H02H1S2SBS3BL12Hr1HS3BOT4LOSP3BL32HcS3BL22Hr2DJ".
split; [lia|]. split; [lia| exact I].
- pose proof (CIB iv Hiv). unfold AIMG_HI in *. split; [lia|]. split; [lia| exact I].
- assert (NE : HB p A n <> b) by (intros E; apply NI; rewrite E; exact Hb).
pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB p A n) b AH (or_introl eq_refl) (or_intror Hb) NE) as DJ. cbn [ab_addr ab_size] in DJ.
pose proof (AI_block_bounds AI _ _ _ _ _ b AH (or_intror Hb)) as BB.
split; [lia|]. split; [lia| exact I].
- assert (A47 : 0 <= a' < 2^47).
{ destruct Ha' as [X|[(iv & Hiv & Hr)|(c & FA & fn & Hb & Hr)]]; [lia| pose proof (CIB iv Hiv); pose proof (AI_aci_lo AI iv Hiv); unfold AIMG_HI in *; lia|].
pose proof (AI_block_bounds AI _ _ _ _ _ _ AH (or_intror Hb)). cbn in *. unfold AIMG_HI in *. atop_facts. lia. }
pose proof (shad_in_band a' A47) as SB. pose proof (ablk_clear_band _ _ (shad a') BR1) as CB0. unfold KLS in *.
split; [intros X; apply CB0; [lia| exact X]|].
split; [rewrite shad_div; unfold ASHOFF; atop_facts; clear - A47 BOT H; Z.div_mod_to_equations; lia| exact I].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Theorem fuzz_malloc_proofA : fuzz_mallocA_stmt.
Proof.
unfold fuzz_mallocA_stmt. intros until lo. intros AH MI ST BOT LOS TOPS SP16 TP A0 Hn HUm RSTK RIMG ROK.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (AI_layout AI _ _ _ _ _ AH) as (LAY1 & LAY2 & LAY3 & LAY4 & _).
pose proof (AI_rtcells AI _ _ _ _ _ AH) as (_ & GOT & _ & _ & SHB & _).
unfold FUZZ_MALLOC_STACK_A, AMALLOC_STACK in LOS. unfold AREQMAX in *.
unfold Harness.fuzz_malloc. Local Ltac2 Set LiaHints.tbl := fun () => "00`0?15785868885.68 20431864004.68 20589229486.68 23477343339.1092431248216.64  25933332553.10627730847314.73 28807746691.10931401241662.10832600174396.70 3527688974.68  3527688974.93  3828146333.109 39949608786.73 40201484047.11840201484047.73 42037126181.68 42831019478.73 43061412648.66 43104399792.73 44030539416.68 45221239098.70 45465607090.68 49532190000.10949978085870.70 51645094794.10651645094794.68 52136437230.70 53367083751.10953767577774.11753767577775.72 54164510851.11654164510851.70 56172361115.66 58035016821.68 59314873579.11059314873579.67 59428837696.68 59583261834.68 61929812114.66 62583080755.73 63235321900.11563235321901.69 65958488200.67 67081926311.70 67442779212.68 67541566890.70 67541566890.73 00000;00<00B00C00G00R00[00g00h00l01;01J01O01X01Y01Z01_01d01i01m02102602702802A02B02C02L02R02W02\02]02^02d02o03603=03>03?03C03D03I03N03]03^04A04F04KS3BOT3LOS1HSS4TOPSSS2HnS4TOPS4LAY3S3BOT3LOSS2Hn3BL13BL3SS2HBS3BOT3LOS3RSP1HS3BOT3LOS3RSP1HS3LOSS3BOT3LOSSSS3LOSS3RSPS3LOSS2HBS2HnS3RSPSSS3BOT3LOSSSS3BOT3LOSS4TOPSS3LOSS3LOSSSS4TOPSS3BOT3LOS1HS3BL11KS2Hn2K0SSS2HnSS3LOSS3LOSS3BOT4TOPS4LAY3SS3BOT3LOS4SP163RSP4LAY14LAY24LAY41HS3LOSS3LOS".
replace (0 <? n) with true by (symmetry; apply Z.ltb_lt; lia).
apply implMA_from_evtF.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (RLO : rng RNG lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| destruct ST as [? _]; lia]).
carve_frame 16%nat ST.
subst a0 tp. unfold AFUZZ_MALLOC.
do 3 zstep.
zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].
zstep. zstep. zstep. zstep.
apply evtF_done.
lazymatch goal with |- implMA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
assert (AH1 : AHEAP AI L RNG (aps_m s) LB mx)
by (eapply (AI_frame AI); [exact AH| exact MU| exact WM| constructor; [left; left; cbn; lia| constructor]])
end.
eapply implMA_bind.
{ eapply (implMA_amalloc_call AI) with (lo := lo) (tr := []); rewrite ?unsigned_lit by lia;
first [ reflexivity | exact AH1 | eassumption | exact ROK
| (apply aunw_data; rewrite ?unsigned_lit by lia; [lia | atop_facts; lia | exact HUm])
| (unfold AMALLOC_PC, AMALLOC_STACK, AREQMAX; cbn; atop_facts; lia)
| (clear - SP16 RSP LOS LAY4 BOT; Z.div_mod_to_equations; lia) ]. }
cbv beta. intros r s' RNG' ms1 [SOE PO].
destruct PO as (LE & u0 & u1 & u2 & xa0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MI2 & ST2 & HPR & RR).
cbn [fst snd] in RR, HPR, ST2, MI2. rewrite ?unsigned_lit in ST2, HPR by lia.
destruct r as [p|]; [| destruct RR].
destruct RR as (A & junk2 & -> & BR & AH2 & BLK & RA & RSA & _).
pose proof BR as (BR1 & BR2 & BR3 & BR4). pose proof (ablk_lin _ _ BR1) as (BL1 & BL2 & BL3 & BL4). unfold AIMG_HI in BL1.
unfold AFMALLOC_RET. retlit.
assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra])
by (eapply aheap_pres_rw_cells; [exact HPR| eassumption| left; left; cbn; lia]).
apply implMA_ret.
pose proof (rng_fp_le _ _ _ _ LE RSTK) as RSTK'.
assert (RLO' : rng RNG' lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact LE| exact RLO]).
zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|].
do 3 zstep. zstep.
release_frame FR2 ST2 (bv_unsigned sp).
apply evtF_done. unfold fuzz_mallocA_post. split; [exact LE|].
do 14 eexists. exists m2, p, A, junk2. split; [reflexivity|]. split; [reflexivity|].
split; [exact MI2|]. split; [exact ST2|].
split.
{ eapply aheap_pres_trans.
- eapply (aheap_pres_frame L RNG (aps_m s) LB m _ _ lo (bv_unsigned sp) AH MU WM); [| exact BOT| lia].
constructor; [cbn; lia| constructor].
- eapply aheap_pres_weaken; [exact HPR| lia| intros b Hb; exact Hb]. }
split; [exact SOE|]. split; [exact BR|]. split; [exact AH2|]. split; [exact BLK|]. split; [exact RA| exact RSA].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Theorem prod_create_proofA : fuzz_mallocA_stmt -> prod_createA_stmt.
Proof.
intros FMALLOC. unfold prod_createA_stmt. intros until lo. intros AH MI ST BOT LOS TOPS SP16 TP HUm RSTK RIMG ROK.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (AI_layout AI _ _ _ _ _ AH) as (LAY1 & LAY2 & LAY3 & LAY4 & _).
pose proof (AI_rtcells AI _ _ _ _ _ AH) as (_ & GOT & _ & _ & SHB & _).
unfold PROD_CREATE_STACK_A, FUZZ_MALLOC_STACK_A, AMALLOC_STACK in LOS.
apply implMA_from_evtF.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
Local Ltac2 Set LiaHints.tbl := fun () => "01U0?10290676280.67 11447730086.16411903774446.71 13040978216.12913814036707.1101410765159.125 1410765160.121 14603864330.12915685060272.72 17221588796.71 17776320428.71 17776320431.12517842804490.1051798228060.67  19006120615.74 19027788829.12721338498993.12923230285244.74 23477343339.11824487705898.11424487705898.11724938099585.10925435258127.12625435258127.72 25566553219.12725566553219.74 27730847314.72 28022624402.12228693974236.11828822767675.11829782367974.12229782367974.12633591671254.11833680001082.71 34272850783.12734292212932.66 36362554441.10538806986883.12538806986883.71 39400830519.11139400830519.11639935291810.11839949608786.72 40340350050.12740340350050.12941161757422.71 41562522430.11741936607280.11842744733806.74 42831019478.72 43061412648.64 43987951406.12643987951406.73 45221239098.74 45294964044.67 45426444089.1274902518540.127 49115058125.11849978085870.74 50290691637.1525180980284.74  52136437230.74 53367083751.11853767577774.12653767577774.73 54618151079.74 55104759171.12755104759171.74 55356802853.12656172361115.64 563227834.74   58049300478.12759178106163.72 59308628304.1  59308628433.1  59587539801.12960130285780.12560130285787.1216166287527.71  61751071971.67 63235321900.12463235321900.70 64405586210.12564405586221.12164425055457.10965504523926.10965958488200.11865958488200.66 66151427842.16 66882158783.11067003974766.74 67264817168.12867360917811.11167360917811.11667541566890.71 67541566890.72 67541566890.74 7197370126.67  7197370126.97  7378845197.122 937398257.152  00000500600?00L00M00N00O00T00X00\00a00f00g00h00i00n01301701801901:01?01@01A01B01C01L01M01R01[01\01]01h01m01n01o02:02;02<02=02>02C02L02M02N02W02X02Y02b02g02l03103603;03^03_03l03m04604M04Q04Z04`04e04j04k04l04m04n05405905>05?05C05G05P05Q05R05S05Y05^05c06F06i06n06o07>07M07]07^07g07h07i07j07o08408908H08W08X08hS3LOSFS3BOT3LOSS3BOT3LOS3BL3SFFS3BL1S2HBS2HBS3LOSS3LOSSSSS3BL4S3BL4S2HBSSSS3BL1SSSSS3BOT3LOSFS3LOSS3BL13BL4SSS4TOPS4LAY3S3RSPSSS4TOPS4LAY3SSSSS3LOSS3BOT3LOSSSS3BOT3LOSSSS3BOT3LOSS3RSPS3LOSS3LOSS3LOSS3RSPS3BOT3LOS4SP163RSP4LAY14LAY24LAY41HSS3BOT3LOS3BL3SS3BOT3LOSS3BOT3BL32A81H2H02H52H6S2HBS3BOT3LOSS4TOPSS3LOSS3LOSSSSSS4TOPSS3RSPS3BL1SS2K1S2K2S3BL13BL4FFSS4TOPSS3LOSS3LOSS3RSP4LAY14LAY24LAY43BR23BL13BL22A8S3RSP4LAY14LAY24LAY43BR23BL13BL22A8S3BL4SS3BOT4TOPS4LAY3S3BOT4TOPS4LAY3S3BR41H2H02H42A8SS3BOT3LOSSSSS3LOSS3LOSS3LOSS3BOT3LOS3RSP1HS3BOT3LOS3RSP1HFS2A82DB2H02H52H6".
assert (RLO : rng RNG lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK| destruct ST as [? _]; lia]).
carve_frame 32%nat ST.
subst tp. unfold APROD_CREATE.
do 5 zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
apply evtF_done.
lazymatch goal with |- implMA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
assert (AH1 : AHEAP AI L RNG (aps_m s) LB mx)
by (eapply (AI_frame AI); [exact AH| exact MU| exact WM| constructor; [left; left; cbn; lia| constructor]])
end.
eapply implMA_post_evtF.
{ eapply (FMALLOC L RNG) with (lo := lo) (n := PRODUCER_SIZE) (LB := LB); rewrite ?unsigned_lit by lia;
first [ reflexivity | exact AH1 | eassumption | exact ROK
| (unfold PRODUCER_SIZE, AREQMAX, FUZZ_MALLOC_STACK_A, AMALLOC_STACK; lia)
| (clear - SP16 RSP LOS LAY4 BOT; Z.div_mod_to_equations; lia) ]. }
cbv beta. intros r s' RNG' ms1 PO.
destruct PO as (LE & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & p & A & junk2 & -> & -> & MI2 & ST2 & HPR & SOE & BR & AH2 & BLK & RA & RSA).
rewrite ?unsigned_lit in ST2, HPR by lia.
pose proof BR as (BR1 & BR2 & BR3 & BR4). pose proof (ablk_lin _ _ BR1) as (BL1 & BL2 & BL3 & BL4). unfold AIMG_HI, PRODUCER_SIZE in *.
unfold APCREATE_RET. retlit.
assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra])
by (eapply aheap_pres_rw_cells; [exact HPR| eassumption| left; left; cbn; lia]).
assert (RLO' : rng RNG' lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact LE| exact RLO]).
destruct (AI_block AI _ _ _ _ _ p A 16 AH2 ltac:(left; reflexivity)) as (_ & _ & _ & _ & BSH & _).
assert (A8 : A mod 8 = 0) by (clear - BR4; Z.div_mod_to_equations; lia).
pose proof (ablock_unpoisoned m2 A 16 BSH A8 ltac:(lia) ltac:(lia) ltac:(lia)) as UNP.
pose proof (unpoisoned8_rd_off m2 A (A + 16) A 0 UNP ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_0_r; exact A8)) as RD0. rewrite Z.add_0_r in RD0.
pose proof (unpoisoned8_rd_off m2 A (A + 16) A 8 UNP ltac:(lia) ltac:(lia) ltac:(clear - A8; Z.div_mod_to_equations; lia)) as RD8.
unfold ASHOFF in RD0, RD8.
pose proof (munch_refl [(A, A + 16); (lo, bv_unsigned sp)] m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
change (Z.to_nat 16) with 16%nat in BLK.
pose proof (rw_cells_split_CB asegs m2 A [] 16 junk2 [] [8%nat; 8%nat] BLK eq_refl) as BLK2. cbn [mk_CB_cells app] in BLK2.
clear BLK.
zstep. zstep. zstep. rewrite zxb_lit by lia. zstep. if_cases K1; zify_cond K1; [exfalso; clear - K1; lia|].
zstep.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
assert (UNP0 : unpoisoned mx A (A + 16))
end.
{ pose proof (ablk_disj_band _ _ BR1) as DB. unfold KLS in DB. eapply unpoisoned_munch; [exact UNP| exact MU2|].
rewrite !shad_div. unfold ASHOFF. cbn [disjoint_from]. atop_facts.
split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia| exact I]. }
clear RD8. pose proof (unpoisoned8_rd_off _ A (A + 16) A 8 UNP0 ltac:(lia) ltac:(lia) ltac:(clear - A8; Z.div_mod_to_equations; lia)) as RD8.
unfold ASHOFF in RD8.
zstep. zstep. zstep. zstep. rewrite zxb_lit by lia. zstep. if_cases K2; zify_cond K2; [exfalso; clear - K2; lia|].
zstep.
do 4 zstep. zstep.
release_frame FR2 ST2 (bv_unsigned sp).
zstep.
apply evtF_done. unfold prod_createA_post. split; [exact LE|].
do 14 eexists. eexists _, p, A. split; [reflexivity|]. split; [reflexivity|].
split; [eassumption|]. split; [exact ST2|].
split.
{ eapply aheap_pres_trans; [eapply (aheap_pres_frame L RNG (aps_m s) LB m _ _ lo (bv_unsigned sp) AH MU WM); [constructor; [cbn; lia| constructor]| exact BOT| lia]|].
eapply aheap_pres_trans; [eapply aheap_pres_weaken; [exact HPR| lia| intros b Hb; exact Hb]|].
eapply aheap_pres_fresh; [exact AH2| exact MU2| exact WM2| exact BOT| lia| lia]. }
split; [exact SOE|]. split; [exact BR|].
split; [eapply (AI_frame AI); [exact AH2| exact MU2| exact WM2|];
constructor; [right; left; exists (HB p A 16); split; [left; reflexivity| cbn; lia]| constructor; [left; left; cbn; lia| constructor]]|].
split; [exact BLK2|]. split; [exact RA| exact RSA].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Theorem prod_free_proofA : prod_freeA_stmt_at APROD_FREE.
Proof.
unfold prod_freeA_stmt_at. intros until tr. intros AH HIN MI ST BOT LOS TOPS TP A0 UC UIN NS8 RA4 RAPC LEN SP16 RSTK ROK.
apply implMA_from_evtF. unfold APROD_FREE. zstep. apply evtF_done.
eapply (implMA_afree_call AI L RNG) with (tr := tr); try eassumption.
apply aunw_chain; assumption.
Qed.
End Stmts.
End CANSEC1.
