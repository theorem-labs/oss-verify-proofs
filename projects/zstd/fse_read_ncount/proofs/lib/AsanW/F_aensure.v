(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import MM_syscalls.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import SysStepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg AProto ABase AKit AKit2 ARep ARepFrame RT_stubs F_apoison F_aalloc3 F_ammap.
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
Local Ltac band_lin :=
repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.
Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
Local Ltac aload ST8 i AEXPR :=
lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
let RD := fresh "RD" in
pose proof (u64arr_read asegs mm A ws i (nth (Z.to_nat i) ws w0) (wa AEXPR) ST8
ltac:(apply nth_error_nth'; rewrite ?upd_length; lia) ltac:(lia) ltac:(f_equal; lia)) as RD;
step; clear RD
end.
Local Ltac astore ST8 i :=
lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
let SOK := fresh "SOK" in
pose proof (u64arr_store_ok asegs mm A ws i (wa (A + 8 * i)) ST8 ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
step;
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) (le8 ?v)) _) =>
let S2 := fresh "STATS" in
pose proof (u64arr_write asegs mm A ws i v ST8 ltac:(rewrite ?upd_length; lia)) as S2;
replace (A + 8 * i)%Z with E in S2 by lia;
clear ST8; store_done; try clear SOK; rename S2 into ST8
end
end.
Section CANSEC1. Context {rc : runConstT}.
Definition ensure_entry := 0x3514c.
End CANSEC1.
Notation ENSURE_STACK := 448 (only parsing).
Section CANSEC2. Context {rc : runConstT}.
Definition m3_cells (L : alayout) (m : amem) : Prop :=
poison_cells m /\ rmap_cells m
/\ rw_cells asegs m 0xa1ce0 [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m 0xa1ce4 [C4 (Z_to_bv 64 0)]
/\ rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] /\ rw_cells asegs m ATSD [C8 (Z_to_bv 64 (al_ctx L))]
/\ rw_cells asegs m (al_ctx L + 152) [C8 (Z_to_bv 64 (al_t L))]
/\ rw_cells asegs m 0x9ee38 [C8 (Z_to_bv 64 (al_space_beg L))]
/\ rw_cells asegs m 0x9ee40 [C4 (Z_to_bv 64 4294967295)]
/\ rw_cells asegs m 0x9ee48 [C8 (Z_to_bv 64 (al_space_beg L + K_SPACE_SIZE))]
/\ rw_cells asegs m 0x9ee50 [C1 (Z_to_bv 8 0)].
#[using="Type"] Lemma m3_cells_frame : forall L m m' W, m3_cells L m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => (AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) /\ (snd iv <= al_ctx L + 152 \/ al_ctx L + 160 <= fst iv)) W -> m3_cells L m'.
Proof.
intros L m m' W (PC & RC & C1' & C2 & C3 & C4' & C5 & C6 & C7 & C8' & C9) MU WM HW.
assert (D : forall A k, 0 <= k -> A + k <= 0x5f7000 -> 0x10000 <= A -> disjoint_from W A k).
{ clear -HW. intros A k Hk HA HA0. unfold AIMG_HI, AIMG_LO in HW. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }
assert (DC : disjoint_from W (al_ctx L + 152) 8).
{ clear -HW. unfold AIMG_HI, AIMG_LO in HW. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }
destruct PC as (P1 & P2 & P3 & P4 & P5 & P6 & P7). destruct RC as (Q1 & Q2 & Q3 & Q4 & Q5).
split; [unfold poison_cells; repeat lazymatch goal with |- _ /\ _ => split end;
(eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; apply D; lia])|].
split; [unfold rmap_cells; repeat lazymatch goal with |- _ /\ _ => split end;
(eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; apply D; lia])|].
unfold ATP88, ATSD in *.
repeat lazymatch goal with |- _ /\ _ => split end;
(eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; first [exact DC | apply D; lia]]).
Qed.
#[using="Type"] Lemma m3_cells_frame_rc : forall L m m' W, m3_cells L m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => (AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) /\ (snd iv <= al_ctx L + 152 \/ al_ctx L + 160 <= fst iv)) W -> rmap_cells m'.
Proof. intros L m m' W MC MU WM HW. exact (proj1 (proj2 (m3_cells_frame L m m' W MC MU WM HW))). Qed.
Definition ensure_ret (L : alayout) (RNG : footprint) (sp : word) (st : astate) (c nf lo : Z) (sj : list word) (m : amem)
(st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
let r := get_cls st c in let FA := afreearr L c in let mfa := c_mapped_free_array r in
fp_le RNG RNG' /\
exists new sj',
( (4 * nf <= mfa /\ new = mfa /\ st2 = st /\ RNG' = RNG)
\/ (mfa < 4 * nf /\ new = rup (4 * nf) K_FREEARR_MAP /\ st2 = put_cls c (cls_set_mapped_free_array new r) st
/\ rw_cells asegs m' (FA + mfa) [CB (Z.to_nat (new - mfa)) (repeat (Z_to_bv 8 0) (Z.to_nat (new - mfa)))]
/\ fill_at m' (shad (FA + mfa)) (shlen (new - mfa)) 0xfa
/\ rng RNG' (FA + mfa) (new - mfa) /\ rng RNG' (shad (FA + mfa)) (shlen (new - mfa)) /\ fp_bw RNG'))
/\ 4 * nf <= new <= K_FREEARR_MAX /\ mfa <= new /\ new mod K_FREEARR_MAP = 0
/\ munch [(bv_unsigned sp - ENSURE_STACK, bv_unsigned sp); (FA + mfa, FA + new); (shad (FA + mfa), shad (FA + mfa) + shlen (new - mfa));
(al_t L + 2800, al_t L + 3168); (aregion_info L c + 24, aregion_info L c + 32)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' (aregion_info L c + 16)
[C8 (Z_to_bv 64 (c_num_freed r)); C8 (Z_to_bv 64 new); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)]
/\ u64arr asegs m' (al_t L + 2800) sj' /\ length sj' = 46%nat
/\ azero m' (shad (FA + new)) (shlen (K_FREEARR_MAX - new))
/\ m3_cells L m'.
#[using="Type"] Lemma rup18_facts : forall x, 0 <= x -> x <= rup x 262144 <= x + 262143 /\ rup x 262144 mod 262144 = 0 /\ (x mod 262144 = 0 -> rup x 262144 = x).
Proof. intros x Hx. unfold rup. Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0010=4151200461.2400000?S1H2H02H42H52H9".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma ensure_spec : forall RNG {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c nf lo : Z) (sj : list word),
let r := get_cls st c in let RI := aregion_info L c in let FA := afreearr L c in let mfa := c_mapped_free_array r in
stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - ENSURE_STACK ->
mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 RI -> a2 = Z_to_bv 64 (aregion L c) -> a3 = Z_to_bv 64 nf ->
m3_cells L m ->
rw_cells asegs m (RI + 16)
[C8 (Z_to_bv 64 (c_num_freed r)); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)] ->
u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
0 <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 -> 0 <= nf -> 4 * nf <= K_FREEARR_MAX ->
0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP ->
(al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
(al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
(al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
AIMG_HI <= al_ctx L ->
iclr (al_t L) 4096 ->
(forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
ensure_ret L RNG sp st c nf lo sj m st2 RNG' m' ->
implS asegs RNG' (aembed ATOP (k st2 true)) (epostF Q)
(MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
implS asegs RNG (aembed ATOP (ensure_free_array st c nf k)) (epostF Q)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ensure_entry) fc None m (seg_rom asegs)).
Proof.
intros until sj. cbv zeta.
intros ST CEIL LO MI TP -> -> -> -> MC REG STATS LSJ AZ SBE HC MFA MFAM NF NF4 SP1 SP2 SP3 CX0 CX1 T0 T1 TCX SCX TSP RIMG RSTK RCTX RT RRI CXI TIC KONT. band_lin.
box TCX. box SCX. box TSP.
pose proof MC as MC0. destruct MC0 as (PC & RC & TI & TK & T88 & TSD & CT & ISB & IREL & ISE & IPRE).
unfold AIMG_HI, AINSTANCE, ATP88, ATSD, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, ensure_entry in *.
change (2^37) with 137438953472 in *.
word_range sp SPR.
set (mfa := c_mapped_free_array (get_cls st c)) in *.
assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
pose proof (munch_refl [(bv_unsigned sp - ENSURE_STACK, bv_unsigned sp)]%Z m) as MU.
pose proof (wmono_refl asegs m) as WM.
iprefix.
Local Ltac2 Set LiaHints.tbl := fun () => "04a0?100583406.101  10345787758.10410345787758.1721047820382.13  10649802198.16310822766052.16610830758748.16 10830758748.19 11777263255.10411797343393.16011797343393.16111799489569.16611805467289.10111805467289.10311805467289.10411805467289.17211805645610.34 11807744665.10 11807744665.16212428150072.1641279872003.10  12854285654.16113339656022.16113824269827.24 14051373607.29 14068158678.16014793086774.11214793086774.14614793086774.16114869079534.10414869079534.17215045184517.16015045184517.16115387613978.17115426709718.16015868313659.24 15868313659.43 16152533917.15816449464117.11216458268297.96 16465181398.16016905242454.16116961996613.26 17277026341.13 1733136316.3   17534156933.16117534156933.16217632079770.10517776320428.16517776320431.10217776320431.10317803025398.15817928269142.16117986879152.13 17986879152.23 1800609155.103 1800609155.104 1800609155.166 18746109209.16618770195838.16519617313304.22 19617313304.37 19878645462.16020313996398.10320416174892.17220431170854.16220794827301.23 20857051927.10321200416232.28 21533188226.10721533188226.17222226902198.16122233892466.17322264047035.8  22389541692.10122430420899.16422634910937.16622700267513.16722706556809.10 22837444294.26 22952216122.17222954650507.6  23253790359.10323255034585.16623868974523.10623868974523.17124336903790.10424487705898.1022452149659.168 24638473347.10424638473347.10524638473347.16724678275670.16024991151882.13625065190167.17 25065190167.18 25065190167.21 25071471268.34 25076071819.16425076071819.16525139969802.19 25571772251.51 26019439157.2  26339595734.16126578924325.11226586770331.10126690313645.15827189741570.16027574660131.16627904909209.15927905056697.96 28132537239.10428417259964.10328554043606.16028718966614.16128891897251.16428927932361.55 28930018938.69 29193796462.10329313596044.23 29928128769.43 30272193814.16131378308326.94 32071826473.17132307613550.10132335205627.11 32335205627.26 32740259714.16133062543571.23 33298494999.10433399844006.16033405859426.17033680001082.10434004991342.10334430152252.10435008968799.29 35042221400.26 35099623001.16635520726249.7  36115622446.10336115622446.10436115622447.16636370459630.10436370459630.17236848298211.1643794754569.5   37952880771.3  3888239342.104 38903098019.16438938709062.26 39693769198.10139922432342.16140457739452.10340672532759.10341168710592.23 41417988426.3  42002647203.16442009006514.1614222606119.5   42238456215.10442805740039.16443059266230.92 4326757543.29  43551704186.23 43607530787.16443913974254.10443913974254.17243987951406.10343987951406.10443987951407.16643988483203.10143988483203.10343988483203.16544181748438.16044487020398.16644500894574.10345221239098.10445221239098.17245297343979.16145625533142.16045848756903.10145889153637.13645889153764.13745947119741.50 46024503395.16746024503395.1694605342103.12  46134254574.10446134254574.17246468661564.10446801997731.3  47241242302.29 47472103150.10447805607814.3  48316456345.17248724676119.10349147187950.10449476425441.17249476425454.16449476970463.29 49649769127.10450310179909.4  50317564526.10350381176099.1645039673326.101 50693720814.10450699409881.16650836217433.16650837928942.10150885398489.12 50978328983.10151318623851.16051583216406.35 51705425809.96 51711223320.95 51721692860.15851811717094.19 51866641414.15852105090727.10352567164907.17252575291859.16052575291859.16152622824343.1015316791447.104 53180773481.7  53381025066.29 5374621895.51  53767577772.16553767577775.10253767577775.10353877920417.16054243526019.10354243526019.10454243526019.16654569212142.10454722921710.10354969794426.13 55113301982.16455225214521.23 55590199162.19 56170256219.11156170256219.14556170256219.1605622855209.111 563227834.103  56718280739.16457622410744.16557628700040.10 57745675194.1035783825422.29  58931178838.16159308579414.13 59308628433.6  59314873579.13 59382628974.1035953130734.104 59792900274.29 60128159214.10460128159214.17260258122606.10360571393319.17260592618094.10360858483367.10461529484705.19 61628829678.10161674577390.10461674577390.17261723695716.6  61957295940.3  6269928558.103 62704248302.10362973951777.16163042061173.4  63235321900.10063235321900.10263235321901.16463255209115.16563305555623.10363713694743.10363776448791.10464997134979.10464997134979.10564997134979.16765141294375.23 66151427842.20 66423386478.1036725418733.5   67663283182.10467663283182.17268055296919.10368096078318.101766265084.1    7850740697.166 8384152046.101 8583720762.101 8684881006.103 8722841838.104 876831355.5    8806423751.9   8875530120.23  9333008750.103 9372136215.101 9561132377.166 9595551854.103 9844715886.103 00000900B00R00Z00[01401@01O01c01d01e02W02X02Y02Z02[03903?03i03j04404=04F04`05305<05K05Z05i06206B06G06L06M06V07407F07K07P07U07^07g08008408808=08B08J08N08R08V08W08`08f08l08m08n08o09<09S09T09U09^09g09h09i09m0:A0:W0:X0:Y0:Z0:[0:j0:n0;@0;M0<j0<n0=:0=>0=F0=S0=`0=e0=j0>30>40>90>:0>;0><0>E0>F0>W0>k0?E0?k0AL0AM0AN0B20B60B?0BO0B`0Be0Bi0Bj0Bn0C20CB0CF0CO0CX0Cj0Ck0Cl0D50DB0De0Df0Dg0Dh0E10E@0EO0ES0ET0Ea0Eb0Ec0Eh0F10F50FB0FF0FS0F\0F`0Fd0Fh0G10GA0GS0GW0G_0Gh0H:0HO0HX0Ha0He0I50I60I70II0IJ0IO0Ic0Id0Ih0Ik0J60JH0JQ0Ja0Je0Ji0Jm0Jn0Jo0K00K90K:0KC0KH0KL0KU0K^0K_0L00LD0LE0LJ0LK0LZ0Lc0M30M70M80ME0MN0MO0Mh0N<0NE0NF0NK0NP0NQ0NR0N[0Nm0O60O?0OL0OY0Ob0Oo0P?0PH0Po0Q00Q10Q20Q30Q40Q50Q60Q70Q80QL0Q\0Qe0R00Rj0Rn0S20S60SB0SC0SD0SE0SN0SW0S\0TB0TG0TR0TW0T\0Ta0Tb0Tg0U90VV0VZ0V_0Vd0Vm0W?0WC0WK0WT0W]0X10X:0XJ0XS0Xn0Y70Y80Y=0YF0YO0Y_0Y`0Yd0Ym0Z60ZB0ZJ0ZN0ZR0ZV0Z[0Z\0Zl0[90[:0[;0[<0[S0[`0[i0[m0\60\F0\S0\\0\]0\j0]30]80]A0]J0]O0]S0]`0]i0^60^C0^L0^US4CEIL2LOS4CEIL2LOS3SP12KC3FA53FA0S3CX12T1SS4CEIL2LO3SP23FA33FA53HspS2HC3FA33FA5S3FA33FA53FA01YS4CEIL2LO2HC3SP23RIESSS4CEIL2LO4SHF24SHF33Hsp3CX13MFA3SP23FA33FA53LSJ2T1SSSSS4CEIL2LO2HC3SP21H2H02H42H52H9S2HC1YS3LSJ3MFA3SP13FA23FA52K14SHF14SHF24SHF32T2FS3FA52P21HS3LSJ3TICS3LSJ3TICS2NF3NF41H2H02H42H52H93H10S2HC3MFA3SP13FA02Y0S3LSJ3TICS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS4CEIL2LOS3SP12KC3FA53FA0S3LSJS3LSJFS3LSJ3TICS2HC3MFA3SP13SP21H2H02H42H52H9S3SP13FA03CX21H2H0S3LSJS3MFAS3MFAS3LSJ3TICS3LSJ3TICS3FA23SHTS2LOS2LOS3LSJS3LSJS2NF3NF4S2LOS2LOS2LOSS3LSJ3TICS4CEILS4CEILSSSS4CEIL2LO3HspS4CEIL2LO4SHF24SHF33HspFFS3LSJ3TICS4CEIL2LOSSS2LOS4CEIL2LO2HC3SP23RIES2HC3SP21H2H02H42H52H9SSSSS4CEIL2LO3CX11HS2HBS4CEIL2LO4SHF13HspS4CEIL2LO3HspS4CEIL2LO3LSJ2HC3MFA4MFAM3NF43SP13SP22T13KE'3RU13RU23RU32KC3FA23FA33FA52K14SHF24SHF32T23Hsp1HS2HxS2HC3SP13SHTS2HBS2HC3MFAS4CEIL2LO3CX1S4CEIL2LO3HspS3RIES3RIES4CEIL2LOSS3LSJSSSS3LSJ3TICSS4CEIL2LO3SP23FA3S4CEIL2LO2HC3SP23FA3S4CEIL2LO3SP22T13FA33FA01YS4CEIL2LO2HC3MFA3SP13SP21H2H02H42H52H9S4CEIL2LO3LSJ3MFA4MFAM3SP13CX13KE'3RU13RU23RU33FA23FA52K14SHF14SHF23CX23Hsp3NF43SP23FA33FA02T12T2FSS4MFAM3RU21H2H02H42H52H93H103H193H24S2NFS3LSJ3TICS3MFA3KE'3RU12KCS3MFA3NF43KE'3RU1S3LSJS2T1FS2LOS2LOS4CEIL2LO3LSJ2T1S2HBS3LSJ3TICS3LSJ3TICS4CEIL2LO4SHF13HspFFS4CEIL2LOS3FA23FA43FA5S3SP13SP23FA33FA03CX21H2H02H42H52H9SSFS4CEIL2LOS4CEIL2LO3SHR1HS4CEIL2LO3SHT1HS2T1SS4CEIL2LO3CX1SSS3SPRS4CEIL2LOS2HBS3MFA3SP13FA0S2SES4CEIL2LO3HspS3KE'3RU1S2LOS2LOS2LOS4CEIL2LOS3SP12KC3FA53FA0S4CEIL2LO4SHF13HspS2KES2NF3NF4S4CEIL2LOS4CEIL2LO4SHF13HspS4SHF14SHF32SE3SHT2T1S4CEIL2LOS3LSJ3TICS2HBS4CEIL2LO3LSJ2T1SSS4CEIL2LO4SHF13HspSS3KE'S4CEIL2LO2HC3SP23RIEFS2LOS1YS3SP23FA31HS4CEIL2LO4SHF13HspS4CEIL2LOS3SP12KC3FA53FA0S2LOS2LOS2LOSSSS3LSJ3TICFS4CEIL2LOS3SPRS2HBS3LSJ3TICS3LSJ3TICSS3SP23FA23FA33FA5S2K23SP23FA23FA33FA5FS3LSJSS3SP23FA33FA51HS4CEIL2LOS3SP12KC3FA53FA0S2HBSS4CEIL2LO3CX1S4CEIL2LOSS4CEIL2LO3MFA3SP23FA33FA5S4CEIL2LO2HC3SP23RIES4CEIL2LOSS3LSJS3TICSSS4CEIL2LOS4CEIL2LO4SHF13HspS4CEIL2LOS4CEIL2LOS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LOS3SP23FA23FA3S4CEIL2LO3LSJ2T1S3LSJ3TICS3SP23FA23FA33FA43FA51H2H02H42H52H93H14FSSSSSSSSS4CEIL2LO2HC3SP23RIES4CEIL2LO3LSJ2T1S3MFA3KE'S4CEIL2LO1HS2HC3MFA4MFAM3SP13SP33KE'3RU13RU22KC1H2H02H42H52H93H143H19S2LOS2LOS2LOS4CEIL2LO2T1SSSS4CEIL2LOS4CEIL2LOS3CXIS4CEIL2LO3SP13SP23FA33FA53FA04SHF23HspS3FA5S3SP23FA31HS3HspS3HspS3HspFS3SPRS4CEIL2LO4SHF13HspS4CEIL2LO3LSJ2HC3MFA4MFAM3NF43SP13SP22T13KE'3RU13RU23RU32KC3FA23FA33FA52K14SHF24SHF32T23Hsp1HS2HxS3SPRS3FA2S3LSJ3TICS3NF43RU13RU22KC1HS2K2S3FA22K1S4CEIL2LOS4CEIL2LOS3SP13FA33FA02Y03CX2S4CEIL2LOS3SP12KC3FA53FA0S4CEIL2LOS3NF43SP13KE'3FA04SHF24SHF3S4CEIL2LOSS3FA2S4CEIL2LOS4CEIL2LOS3SP12KC3FA53FA0SS2KCS4CEIL2LOS4CEIL2LOS4CEIL2LO2T1S3RU12KCS2LOS2LOS2LOS3LSJSS4CEIL2LO3LSJ2T1S4CEIL2LO3CX1SSSS3KE'3RU12KC1H2H02H42H5S3FA11H2H02H4S4CEIL2LOS2KES4CEIL2LOS3SP12KC3FA53FA0S4CEIL2LO3CX1S4CEIL2LOSS4CEIL2LO3HspS4CEIL2LOS3SPRS4CEIL2LOS4CEIL2LOS3KE'S2HxS3FA13FA23FA5S4CEIL2LOS4CEIL2LO3CX1S4CEIL2LO3HspS4CEIL2LOS4CEIL2LO".
carve_frame 48%nat ST.
step. step. step. step. step. step.
rewrite RIE in REG |- *. rewrite FAE in AZ.
step.
zstep. step.
step. if_cases KE; zify_cond KE.
{
assert (KE' : 4 * nf <= mfa) by (rewrite Z.shiftl_mul_pow2, Z.mod_small in KE by (clear -NF NF4; lia); clear -KE; lia). clear KE.
step. step. step. step. step. step. step. step.
lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -48) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
apply evtF_done. unfold ensure_free_array.
replace (nf * 4 <=? c_mapped_free_array (get_cls st c)) with true by (symmetry; apply Z.leb_le; fold mfa; clear -KE'; lia).
eapply KONT. unfold ensure_ret, K_FREEARR_MAX, K_FREEARR_MAP. cbv zeta. fold mfa. split; [apply fp_le_refl|].
exists mfa, sj. split; [left; split; [exact KE'| split; [reflexivity| split; reflexivity]]|].
split; [clear -KE' MFA NF4; lia|]. split; [clear; lia|]. split; [exact MFAM|].
rewrite FAE, RIE.
split. { eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. clear. intros x Hx. tauto. } split; [assumption|]. split; [assumption|]. split; [assumption|].
split; [assumption|]. split; [assumption|]. split; [exact LSJ|].
split.
- eapply azero_frame; [exact AZ | exact MU | exact WM |]. intros Hp. cbn [disjoint_from].
assert (SHR : 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)
/\ shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa) + shlen (536870912 - mfa) <= 0x10007fff8000).
{ rewrite shad_div, shlen_div. unfold ASHOFF. clear -SP1 SP2 HC MFA. Z.div_mod_to_equations. lia. }
clear -SHR CEIL LO. split; [lia| exact I].
- eapply m3_cells_frame; [exact MC | exact MU | exact WM |].
apply Forall_cons; [cbn [fst snd]; clear -CEIL LO CX1; unfold AIMG_HI, AIMG_LO; lia | apply Forall_nil]. }
assert (KE' : mfa < 4 * nf) by (rewrite Z.shiftl_mul_pow2, Z.mod_small in KE by (clear -NF NF4; lia); clear -KE; lia). clear KE.
pose proof (rup18_facts (4 * nf) ltac:(clear -NF; lia)) as (RU1 & RU2 & RU3).
set (new := rup (4 * nf) 262144) in *.
zstep. zstep. zstep. zstep. zstep.
setreg 8 (Z_to_bv 64 new) ltac:(rewrite Z.shiftl_mul_pow2, land_align2p18 by (clear -NF NF4; lia); f_equal;
subst new; unfold rup; clear -NF NF4; Z.div_mod_to_equations; lia).
zstep. zstep. step. if_cases KC; zify_cond KC. { exfalso. clear -KC RU1 RU2 NF4. Z.div_mod_to_equations. lia. }
lstep.
zstep. zstep. zstep. zstep.
unfold aregion, K_REGION. change (2^32) with 4294967296.
setreg 9 (Z_to_bv 64 (al_space_beg L + c * 4294967296 + 3758096384 + mfa)) ltac:(f_equal; clear; lia).
step. if_lit.
step. zstep. step. step. step. step.
step.
apply evtF_done. unfold ensure_free_array.
replace (nf * 4 <=? c_mapped_free_array (get_cls st c)) with false by (symmetry; apply Z.leb_gt; fold mfa; clear -KE'; lia).
replace (rup (nf * 4) K_FREEARR_MAP) with new by (subst new; unfold K_FREEARR_MAP; f_equal; clear; lia).
replace (K_FREEARR_MAX <? new) with false by (symmetry; apply Z.ltb_ge; unfold K_FREEARR_MAX; clear -KC; lia).
cbv iota. unfold ev. rewrite aembed_vis. cbn [aev_tree]. unfold PROT_RW, F_FIXED.
unfold region_beg, K_REGION, K_FREEARR_OFF. change (2^32) with 4294967296. rewrite SBE. fold mfa.
set (FAM := al_space_beg L + c * 4294967296 + 3758096384 + mfa) in *.
assert (FAM8 : FAM mod 4096 = 0 /\ 0x10007fff8000 <= FAM /\ FAM + (new - mfa) <= al_space_beg L + 137438953472 /\ (new - mfa) mod 4096 = 0 /\ 0 < new - mfa).
{ subst FAM. clear -SP1 SP3 HC MFA MFAM KE' RU1 RU2 KC NF. Z.div_mod_to_equations. lia. }
destruct FAM8 as (FA1 & FA2 & FA3 & FA4 & FA5).
assert (FA0 : al_space_beg L + 4096 <= FAM) by (unfold FAM; clear -HC MFA; lia).
name_sp sp (-48).
eapply rmap_spec with (addr := FAM) (size := new - mfa) (lo := lo).
all: try lazymatch goal with
| |- stk _ _ _ _ => rewrite Hsp; eassumption
| |- ATOP <= _ => atop_facts; exact CEIL
| |- _ <= bv_unsigned _ - _ => rewrite Hsp; clear -LO; lia
| |- mem_inv _ _ => assumption
| |- rmap_cells _ => eapply m3_cells_frame_rc; [exact MC | exact MU | exact WM | apply Forall_cons; [cbn [fst snd]; clear -CEIL LO CX1; unfold AIMG_HI, AIMG_LO; lia | apply Forall_nil]]
| |- rng_aimg _ => exact RIMG
| |- rng _ _ _ => solve_rng
| |- @eq word _ _ => reflexivity
| |- _ mod 4096 = 0 => assumption
| |- 0 < _ - _ => exact FA5
end.
all: try (unfold AIMG_HI; clear -FA1 FA2 FA3 FA4 FA5 SP2 CEIL LO; rewrite ?unsigned_lit by lia; lia).
{
intros a RNG' ms' NE P1 P2. unfold fixed_answer_ok, is_err, TWO64.
replace (2 ^ 64 - 4096 <? a) with false by (symmetry; apply Z.ltb_ge; clear -P2 FA5; atop_facts; lia).
replace (a =? FAM) with false by (symmetry; apply Z.eqb_neq; exact NE). cbn [negb orb]. rewrite aembed_aundef_. apply implF_ret_unr. }
intros RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' RP.
destruct RP as (FPLE & _ & MU2 & WM2 & MI2 & ST2 & ZNEW & GR1 & GR2 & BW & RC2). unname_sp.
apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RCTX.
apply (rng_fp_le _ _ _ _ FPLE) in RT. apply (rng_fp_le _ _ _ _ FPLE) in RRI.
xport FR MU2 WM2 ltac:(clear -SPR CEIL LO FA2 FA3 SP2; lia).
xport REG MU2 WM2 ltac:(clear -SPR CEIL LO FA2 FA3 SP2 HC; lia).
xport STATS MU2 WM2 ltac:(rewrite LSJ; ub TSP; clear -SPR CEIL LO FA0 FA2 FA3 SP2 T0 T1 Y; lia).
clear ST. rename ST2 into ST.
assert (AZ2 : azero m2 (shad FAM) (shlen (536870912 - mfa))).
{ eapply azero_frame; [eapply azero_frame; [exact AZ | exact MU | exact WM |] | exact MU2 | exact WM2 |];
intros _; cbn [disjoint_from]; subst FAM; rewrite ?shad_div, ?shlen_div; unfold ASHOFF;
clear -SPR CEIL LO SP1 SP2 HC MFA KC RU1 KE'; Z.div_mod_to_equations; lia. }
assert (MUF : munch [(bv_unsigned sp - ENSURE_STACK, bv_unsigned sp); (FAM, FAM + (new - mfa)); (shad FAM, shad FAM + shlen (new - mfa));
(al_t L + 2800, al_t L + 3168); (al_space_beg L + 137438953472 + c * 128 + 24, al_space_beg L + 137438953472 + c * 128 + 32)]%Z m m2).
{ eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; clear; intros x Hx; lia. }
clear MU MU2. pose proof (wmono_trans _ _ _ _ WM WM2) as WMF. clear WM WM2.
assert (WOK : Forall (fun iv => (AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) /\ (snd iv <= al_ctx L + 152 \/ al_ctx L + 160 <= fst iv))
[(bv_unsigned sp - ENSURE_STACK, bv_unsigned sp); (FAM, FAM + (new - mfa)); (shad FAM, shad FAM + shlen (new - mfa));
(al_t L + 2800, al_t L + 3168); (al_space_beg L + 137438953472 + c * 128 + 24, al_space_beg L + 137438953472 + c * 128 + 32)]%Z).
{ ub TCX. ub SCX. unfold AIMG_HI, AIMG_LO.
do 5 (apply Forall_cons; [cbn [fst snd]; clear -CEIL LO CX0 CX1 T0 T1 TIC SP1 SP2 HC MFA FA0 FA2 FA3 KC Y Y0;
with_band CX0 ltac:(rewrite ?shad_div, ?shlen_div; unfold ASHOFF; split; Z.div_mod_to_equations; lia) |]). apply Forall_nil. }
pose proof (m3_cells_frame L m m2 _ MC MUF WMF WOK) as MC2.
clear TI TK T88 TSD CT ISB IREL ISE IPRE.
pose proof MC2 as MC2'. destruct MC2' as (PC2 & _ & TI & TK & T88 & TSD & CT & ISB & IREL & ISE & IPRE). unfold ATP88, ATSD in T88, TSD.
replace (ret_pc (Z_to_bv 64 217580)) with (Z_to_bv 64 217580 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
iprefix.
step. if_cases K1; zify_cond K1. { exfalso. clear -K1 FA2 FA3 SP2. rewrite ?unsigned_lit in K1 by lia. lia. }
step. step. if_cases K2; zify_cond K2. { exfalso. clear -K2. lia. }
step. step. step.
pose proof (azero_cb m2 _ _ (shlen (new - mfa)) AZ2 ltac:(rewrite !shlen_div; clear -MFA KC KE' RU1; Z.div_mod_to_equations; lia)) as SHCB.
clear AZ2.
assert (SHF : 0x2008fff7000 <= shad FAM /\ shad FAM + shlen (new - mfa) <= 0x10007fff8000 /\ 0 < shlen (new - mfa)).
{ rewrite shad_div, shlen_div. unfold ASHOFF. clear -FA2 FA3 FA4 FA5 SP2. Z.div_mod_to_equations. lia. }
destruct SHF as (SHF1 & SHF2 & SHF3).
step. with_band CX0 ltac:(with_band T0 ltac:(call_sp (poison_shadow_spec RNG' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FAM (new - mfa) 250 lo))).
all: try lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => first [assumption | unfold ablk; right; clear -FA2 FA3 SP2; lia]
| |- stk _ _ _ _ => eassumption
| |- mem_inv _ _ => assumption
| |- poison_cells _ => exact PC2
| |- @eq word _ _ => reflexivity
| |- rw_cells _ _ (shad _) _ => exact SHCB
| |- rng _ (shad _) _ => exact GR2
| |- rng _ _ _ => solve_rng
end.
all: try (atop_facts; clear -FA1 FA2 FA3 FA4 FA5 SP2 CEIL LO KC RU1 KE' MFA; rewrite ?shlen_div; first [lia | Z.div_mod_to_equations; lia]).
step. with_band T0 ltac:(call_sp (thread_stats_spec RNG' (al_ctx L) (al_t L) lo)).
all: try lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption
| |- stk _ _ _ _ => eassumption
| |- mem_inv _ _ => assumption
| |- @eq word _ _ => first [reflexivity | exact TP]
| |- rw_cells _ _ _ _ => assumption
| |- rng _ _ _ => solve_rng
end.
all: try (unfold AIMG_HI; clear -CEIL LO CX0 CX1 T0 T1 CXI TIC; lia).
all: match goal with |- ?G => idtac "REMT" G end.
aload STATS 10 (al_t L + 2800 + 80). aload STATS 9 (al_t L + 2800 + 72).
zstep. zstep.
snapshot [(al_t L + 2800, al_t L + 3168)]%Z MUs WMs.
box CT. box ZNEW. box REG.
lazymatch goal with P : rw_cells asegs _ (shad FAM) _ |- _ => rename P into SHPO end. box SHPO.
astore STATS 9. astore STATS 10.
carry SHPO MUs WMs ltac:(with_band T0 ltac:(lia)).
carry REG MUs WMs ltac:(ub TSP; clear -HC T0 T1 SP1 SP2 Y; lia).
carry CT MUs WMs ltac:(ub TCX; clear -HC CX0 CX1 T0 T1 Y; lia).
carry ZNEW MUs WMs ltac:(ub TSP; clear -HC T0 T1 SP1 SP2 FA0 FA2 FA3 FA5 Y; lia).
clear MUs WMs.
snapshot [(al_space_beg L + 137438953472 + c * 128 + 24, al_space_beg L + 137438953472 + c * 128 + 32)]%Z MUr WMr.
box CT. box ZNEW. box STATS.
step. step.
carry CT MUr WMr ltac:(ub SCX; clear -HC CX0 CX1 SP1 SP2 Y; lia).
carry ZNEW MUr WMr ltac:(clear -HC SP1 SP2 FA0 FA2 FA3 FA5; lia).
carry STATS MUr WMr ltac:(rewrite ?upd_length, LSJ; ub TSP; clear -HC T0 T1 SP1 SP2 Y; lia).
clear MUr WMr.
step. step.
step. step. step. step. step. step. step.
lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -48) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
apply evtF_done.
unfold fixed_answer_ok, is_err, TWO64. rewrite Z.eqb_refl.
replace (2 ^ 64 - 4096 <? FAM) with false by (symmetry; apply Z.ltb_ge; clear -FA3 FA5 SP2; lia). cbn [negb orb].
eapply KONT. unfold ensure_ret, K_FREEARR_MAX, K_FREEARR_MAP. cbv zeta. fold mfa. split; [exact FPLE|].
lazymatch goal with |- context [u64arr asegs _ _ ?ws] => idtac | H : u64arr asegs _ (al_t L + 2800) ?ws |- _ => exists new, ws end.
rewrite FAE, RIE. fold FAM.
split. { right. split; [exact KE'|]. split; [subst new; f_equal; clear; lia|]. split; [reflexivity|].
split; [exact ZNEW|]. split; [assumption|]. split; [exact GR1|]. split; [exact GR2| exact BW]. }
split; [clear -RU1 KC; lia|]. split; [clear -RU1 KE'; lia|]. split; [exact RU2|].
split. { eapply munch_weaken; [| exact MUF]. unfold sub_fp, FAM. cbn [outside]. clear. intros x Hx. lia. }
split; [assumption|]. split; [assumption|]. split; [assumption|].
split; [assumption|]. split; [assumption|]. split; [rewrite ?upd_length; exact LSJ|].
split.
{ pose proof (azero_split m _ _ (shlen (new - mfa)) AZ ltac:(rewrite !shlen_div; clear -MFA KC KE' RU1; Z.div_mod_to_equations; lia)) as AZT.
replace (shad FAM + shlen (new - mfa)) with (shad (FAM + (new - mfa))) in AZT by (apply shad_add_shlen; clear -FA1; Z.div_mod_to_equations; lia).
replace (shlen (536870912 - mfa) - shlen (new - mfa)) with (shlen (536870912 - new)) in AZT by (rewrite !shlen_div; clear -FA4 MFAM RU2 MFA; Z.div_mod_to_equations; lia).
replace (al_space_beg L + c * 4294967296 + 3758096384 + new) with (FAM + (new - mfa)) by (unfold FAM; clear; lia).
eapply azero_frame; [exact AZT | exact MUF | exact WMF |]. intros Hp. cbn [disjoint_from].
pose proof (shad_add_shlen FAM (new - mfa) ltac:(clear -FA1; Z.div_mod_to_equations; lia)) as SE.
assert (SHT : shad (FAM + (new - mfa)) + shlen (536870912 - new) <= 0x10007fff8000).
{ rewrite shad_div, shlen_div. unfold ASHOFF, FAM. clear -SP2 KC RU1 MFA HC KE'. Z.div_mod_to_equations. lia. }
clear -SE SHT SHF1 SHF2 SHF3 CEIL LO FA2 FA3 FA5 T0 SP1 SP2 HC. with_band T0 ltac:(repeat split; lia). }
eapply m3_cells_frame; [exact MC | eassumption | eassumption | exact WOK].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC2.
