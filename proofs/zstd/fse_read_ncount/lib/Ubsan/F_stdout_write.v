(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac ITree Nodes Decode SysStep MonadX.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad Stdio.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import F_fmt_fp_lib.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import F_syscalls F_stdio_write StdioFiles Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).
Definition wfn_of (so : stdout_st) : Z := if so_first so then F_STDOUT_WRITE else F_STDIO_WRITE.
Definition lbf_of (so : stdout_st) : Z := if so_lbf_nl so then 10 else 0xffffffff.
Definition stdout_cells (so : stdout_st) (flags mode : word) (tail : list byte) : list cell :=
file_cells flags (RSTDOUT_BUF + 1024) (RSTDOUT_BUF + zlength (so_buf so)) RSTDOUT_BUF (wfn_of so) RSTDOUT_BUF 1024 1 mode (lbf_of so) tail.
Definition STDOUT_WRITE_DEPTH : Z := 144.
Ltac fix_lit_store :=
try (lazymatch goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
end).
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Lemma rw_cells_recast : forall m A cs cs',
rw_cells usegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
rw_cells usegs m A cs'.
Proof. intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf'| rewrite Eb; exact Hb] | rewrite Es; exact Hw]. Qed.
Lemma C4_low32 : forall (a b : word) , bv_unsigned a mod 2^32 = bv_unsigned b mod 2^32 -> cbytes (C4 a) = cbytes (C4 b).
Proof.
intros a b E. cbn [cbytes]. unfold le4.
rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned a) 32), <- (Z_to_le_bytes_mod 4 (bv_unsigned b) 32) by (cbn; lia).
rewrite E. reflexivity.
Qed.
Lemma rw_cells_C4_eq : forall m A pre (a b : word) post,
bv_unsigned a mod 2^32 = bv_unsigned b mod 2^32 ->
rw_cells usegs m A (pre ++ C4 a :: post) -> rw_cells usegs m A (pre ++ C4 b :: post).
Proof.
intros m A pre a b post E H. eapply rw_cells_recast; [exact H| | |].
- destruct H as [[Hwf _] _]. apply cells_wf_app in Hwf. apply cells_wf_app. destruct Hwf as [H1 H2]. split; [exact H1|]. exact H2.
- rewrite !cells_bytes_app. cbn [cells_bytes]. rewrite (C4_low32 a b E). reflexivity.
- rewrite !cells_size_app. reflexivity.
Qed.
Ltac fix_lbf FC :=
lazymatch type of FC with rw_cells ?sg ?m' ?A ?cs =>
lazymatch cs with ?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?c16 :: ?c17 :: ?c18 :: ?c19 :: ?c20 :: C4 (Z_to_bv 64 (-1)) :: ?rest =>
apply (rw_cells_C4_eq m' A [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16; c17; c18; c19; c20]
(Z_to_bv 64 (-1)) (Z_to_bv 64 4294967295) rest ltac:(vm_compute; reflexivity)) in FC
end
end.
Lemma rw_cells_C4_CB4 : forall m A (v : word) cs,
rw_cells usegs m A (C4 v :: cs) -> rw_cells usegs m A (CB 4 (le4 v) :: cs).
Proof.
intros m A v cs [[W B] R]. split; [split|].
- cbn [cells_wf cell_wf] in *. split; [apply length_le4| exact (proj2 W)].
- exact B.
- exact R.
Qed.
Lemma firstn1_le4 : forall v : word, firstn 1 (skipn 0 (le4 v)) = le1 v.
Proof. intros v. reflexivity. Qed.
Lemma flags_byte_and64 : forall flags : word,
Z.land (bv_unsigned flags) 64 = 0 -> Z.land (bv_unsigned flags mod 256) 64 = 0.
Proof.
intros flags H. change 256 with (2 ^ 8). Local Ltac2 Set LiaHints.tbl := fun () => "0010=63374621462.2000001S".
rewrite <- Z.land_ones by lia.
rewrite (Z.land_comm _ (Z.ones 8)), <- Z.land_assoc, (Z.land_comm (Z.ones 8)), Z.land_ones by lia.
rewrite H. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma rw_cells_CB4_C4 : forall m A (v : word) cs,
rw_cells usegs m A (CB 4 (le4 v) :: cs) -> rw_cells usegs m A (C4 v :: cs).
Proof.
intros m A v cs [[W B] R]. split; [split|].
- cbn [cells_wf cell_wf] in *. split; [exact I| exact (proj2 W)].
- exact B.
- exact R.
Qed.
Section StdoutWrite.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Hypothesis get_set : forall s so, get_so (set_so so s) = so.
Hypothesis set_set : forall s so so', set_so so' (set_so so s) = set_so so' s.
Definition so_after (so : stdout_st) : stdout_st :=
mkStdout true [] (if so_first so then false else so_lbf_nl so) false.
Definition stdout_writefn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(flags mode : word) (tail : list byte) (l : Z) (lo : Z) (canary : word) (m : mem) (st : St)
: unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 l) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [(bv_unsigned sp - STDOUT_WRITE_DEPTH, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' lo (bv_unsigned sp)
/\ rw_cells usegs m' RSTDOUT (stdout_cells (so_after (get_so st)) flags mode tail)
/\ ssp_cells m' canary
/\ st' = set_so (so_after (get_so st)) st.
#[using="get_set set_set"] Lemma stdout_writefn_spec :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
(flags mode : word) (tail : list byte) (s : list Z) (S lo : Z) (canary : word),
let so := get_so st in
so_active so = true ->
rw_cells usegs m RSTDOUT (stdout_cells so flags mode tail) ->
Z.land (bv_unsigned flags) 64 = 0 ->
bytes_at usegs m RSTDOUT_BUF (to_bytes (so_buf so)) -> (zlength (so_buf so) <= 1024) ->
bytes_at usegs m S (to_bytes s) ->
a0 = Z_to_bv 64 RSTDOUT -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlength s) ->
stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - STDOUT_WRITE_DEPTH) -> (0x50000 <= lo) ->
ssp_cells m canary -> mem_inv usegs m ->
(0 <= S < 2^64) -> (S + zlength s <= 2^64) ->
(bv_unsigned sp < 2^47) -> (S + zlength s <= 2^47) ->
(s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= RSTDOUT \/ RSTDOUT + 232 <= S))) ->
implM usegs (stdout_writefn get_so set_so s) st
(stdout_writefn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc flags mode tail (zlength s) lo canary m st)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (wfn_of so)) fc None m (seg_rom usegs)).
Proof.
intros until canary. cbv zeta. intros ACT FC FL64 BUFB BUFL SRC -> -> -> ST LO GLO SSP MI S0 Shi SP47 S47 SEPS.
pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
destruct SSP as [GOT GUARD]. change usegs with usegs in GOT, GUARD. unfold got_ssp, ssp_guard, STDOUT_WRITE_DEPTH in *.
pose proof (bytes_at_bound _ _ _ _ SRC) as BS. unfold to_bytes in BS. rewrite length_map in BS.
assert (LSB : length (to_bytes s) = length s) by (unfold to_bytes; apply length_map).
unfold stdout_writefn. apply implM_rdso.
unfold stdout_cells, wfn_of, lbf_of in *.
destruct (so_first (get_so st)) eqn:FIRST.
-
apply implM_bind_assoc. apply implM_updso. apply implM_bind_assoc.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] m) as MU.
pose proof (wmono_refl usegs m) as WM.
apply implM_sysk.
change (bytes_at usegs m S (to_bytes s)) with (boxed (bytes_at usegs m S (to_bytes s))) in SRC.
change (bytes_at usegs m RSTDOUT_BUF (to_bytes (so_buf (get_so st)))) with (boxed (bytes_at usegs m RSTDOUT_BUF (to_bytes (so_buf (get_so st))))) in BUFB.
assert (LBB : length (to_bytes (so_buf (get_so st))) = length (so_buf (get_so st))) by (unfold to_bytes; apply length_map).
unfold file_cells in FC. apply rw_cells_C4_CB4 in FC.
Local Ltac2 Set LiaHints.tbl := fun () => "01W0?10964954211.67 10966888420.76 1226947101.76  13468504806.88 1702595686.83  17221588796.76 18926697116.67 18928695579.76 19006120615.79 19246642144.72 22948830513.83 23230285244.78 24440526862.76 24442723209.67 25071629079.76 25071629079.78 25071629079.79 25071629079.83 25071629079.88 25080086061.98 25566553219.10725566553219.79 26757167854.76 27628214043.76 27630474396.67 28044327893.77 28786468985.67 28788403198.76 29419136540.67 29421397403.76 29514832494.78 29572283170.67 31575836224.67 31578097095.76 32377744366.79 33595931868.67 33680001082.76 34290115814.70 3640025710.78  36412203189.76 36414202674.67 37477990236.76 37480185051.67 37738008046.79 38806986883.10638806986883.76 39941652002.99 40259163999.76 40295634780.76 40297567451.67 41072247790.79 41562522430.98 42149039858.76 42151038325.67 43061773371.68 43490452582.83 44713017681.77 4498443158.99  45221239098.79 46356275438.76 48996669764.83 49922148072.68 49924081007.77 50052274856.76 50096175936.67 50280742294.76 50684858817.88 51359702632.76 51361635823.67 5180980284.79  52155062597.68 52670875713.83 54070922032.97 5419307287.67  5421568656.76  54618151079.78 54937879236.88 55067441390.76 55104759171.10755104759171.78 563227834.78   57581223022.78 57622410744.10057622410744.90 57652511122.76 57654444565.67 59310682963.76 60300506080.72 61572084401.88 6166287527.76  63772290790.88 64303108851.74 64303108851.76 64305041780.67 64318189174.72 64616299737.72 7186541364.97  7190913411.76  8084399232.67  8086398727.76  8529237941.76  9279251259.76  942449714.76   00000100200300400500900>00?00D00E00F00J00S00`00a00b00c00d00e00m00n01301;01<01A01W01d01m02202302;02<02J02X02`02j03003503=03>03C03D03I03Q03R03W03[03a03b03g03o04004504>04F04G04O04P04V04^04_04k05305705?05@05H05I05J05N05Z05b05c05d05e05j05k06306406906?06G06J06Q06R06W06_06`06a06f06g06k07307?07@07A07N07[07d07i07j07n08?FFFSSS2HBS3LBBSS3LBBSSS2HBS3S473LSBS3S473LSB3LBBSSSSSS2LO3GLOSS3LBBS2LO3GLOSS3LBBS2LO3GLO4SEP14SEP23LSBS3Shi3LSB3LBBS3Shi3LSBS3LBBSS2LO3GLOFS4BUFL3GLO3LBBS4BUFL3GLO3LBBS2LO3GLOS4SP473LBBS4SP47S3LBBS2LO3GLOSS3LBBSS3LBBS2LO3GLOSS3LBBS2LOS4SP47SS3LBBS2LO3GLOSS3GLOS3GLO3LBBS2LO3LBBSS2S13LSBSS4SP47S2LO3GLOSS2S23LSB3LBBS2S23LSBS2LOS2LO3LBBFS2LO3GLOFFS2HBS2S13LSB3LBBS2LO3GLOSFFS3LBBSS2LO3GLOSS3LBBS4SP47S2LO3GLOS1HS3LBB1HSS3LBBS2He3He0SSS3LBBSS2S0S2S03LSBS2S03LSB3LBBSSS2LO3GLO4SP47S2LO3GLO4SP47S3GLO3LBBS3GLOFS2HeS4BUFL2LO3GLO3LBB".
carve_frame 32%nat ST.
do 9 step. rewrite firstn1_le4, zext_extract_le1. unfold zx8.
step. step. step. fix_lit_store. step.
if_cases Hsvb; zify_cond Hsvb. 1:{ exfalso. exact (Hsvb (flags_byte_and64 flags FL64)). }
do 10 step. step_ecall.
replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (symmetry; apply sx32_small; lia).
split. { at_node_red; split_spine; try reflexivity; try lia. }
intros rsp ans Hdec. unfold dec_ioctl in Hdec. apply dec_plain_Some in Hdec as [ci Hdec].
destruct ans as [e|v]. 2:{ exfalso. destruct Hdec as (_ & Hok & _). discriminate Hok. }
destruct Hdec as [-> He]. unfold efferr, eff0. cbv iota.
apply implM_updso.
unfold implM. apply impl_from_evt. sys_nret.
do 5 step.
if_cases He0; zify_cond He0. 1:{ exfalso. rewrite unsigned_errno_ret in He0 by lia. lia. }
step. step.
fix_lbf FC.
step. apply evt_done.
rewrite !get_set, !set_set. cbn [so_active so_buf so_first].
unfold stdout_stdio_write. apply (implM_rdso usegs get_so). rewrite get_set. cbn [so_buf].
apply rw_cells_CB4_C4 in FC.
eapply implM_bind.
{ eapply (stdio_write_spec (St:=St)) with (B := RSTDOUT_BUF) (fd := 1) (Fp := RSTDOUT) (buf := so_buf (get_so st)) (s := s) (S := S)
(lo := lo) (canary := canary) (wend := RSTDOUT_BUF + 1024) (bufsize := 1024) (mode := mode) (lbf := 0xffffffff) (tail := tail)
(flags := flags) (wfn := F_STDIO_WRITE); try reflexivity; rewrite ?unsigned_lit by lia.
all: first [ exact FC | exact ST | exact MI | exact BUFL | split; [exact GOT | exact GUARD]
| lia | unfold STDIO_WRITE_DEPTH; lia | unfold GLOBALS_TOP; lia | unfold got_ssp; lia | unfold ssp_guard; lia
| unfold boxed in BUFB; apply (bytes_at_transport _ _ _ _ _ _ BUFB MU); cbn [disjoint_from]; rewrite LBB; unfold zlength in BUFL; lia
| destruct SEPS as [-> | [S1 S2]]; [left; reflexivity | right; split; lia]
| right; unfold zlength in BUFL |- *; split; lia
| src_now SRC SEPS MU LSB ]. }
cbv beta. intros [] st' ms' PO.
destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
rewrite !unsigned_lit in MU2, ST2 by lia.
apply implM_upd. rewrite !get_set, !set_set. cbn [so_lbf_nl so_first].
replace (ret_pc (Z_to_bv 64 0x17750)) with (Z_to_bv 64 0x17750 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
destruct SSP2 as [GOT2 GUARD2]. change usegs with usegs in GOT2, GUARD2. unfold got_ssp, ssp_guard in GOT2, GUARD2.
assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -32) [CB 8 (firstn 8 (firstn 16 (firstn 24 junk))); C8 canary; C8 s0; C8 ra]).
{ eapply (rw_cells_transport usegs _ _ m2); [exact FR | exact MU2 | exact WM2 | cbn; unfold STDIO_WRITE_DEPTH in *; lia]. }
step. step. step. if_false. step. step. step. step.
release_frame FR2 ST2 (bv_unsigned sp).
unfold stdout_writefn_post, so_after, stdout_cells, wfn_of, lbf_of, file_cells. rewrite FIRST. cbn [so_first so_buf so_lbf_nl].
sys_finish.
+ apply (munch_trans _ m m0 m2).
* eapply munch_weaken; [| exact MU]. unfold sub_fp, STDIO_WRITE_DEPTH, STDOUT_WRITE_DEPTH in *; cbn [outside]; intros; lia.
* eapply munch_weaken; [| exact MU2]. unfold sub_fp, STDIO_WRITE_DEPTH, STDOUT_WRITE_DEPTH in *; cbn [outside]; intros; lia.
+ eapply wmono_trans; [exact WM | exact WM2].
+ split; [exact GOT2 | exact GUARD2].
+ rewrite ?set_set. reflexivity.
-
apply (implM_retb usegs). unfold stdout_stdio_write. apply (implM_rdso usegs get_so).
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] m) as MU.
assert (LBB : length (to_bytes (so_buf (get_so st))) = length (so_buf (get_so st))) by (unfold to_bytes; apply length_map).
eapply implM_bind.
{ eapply (stdio_write_spec (St:=St)) with (B := RSTDOUT_BUF) (fd := 1) (Fp := RSTDOUT) (buf := so_buf (get_so st)) (s := s) (S := S)
(lo := lo) (canary := canary) (wend := RSTDOUT_BUF + 1024) (bufsize := 1024) (mode := mode) (lbf := if so_lbf_nl (get_so st) then 10 else 4294967295) (tail := tail)
(flags := flags) (wfn := F_STDIO_WRITE); try reflexivity; rewrite ?unsigned_lit by lia.
all: try first [ exact FC | exact ST | exact MI | exact BUFL | exact BUFB | exact SRC | split; [exact GOT | exact GUARD]
| lia | unfold STDIO_WRITE_DEPTH in *; lia | unfold GLOBALS_TOP; lia | unfold got_ssp; lia | unfold ssp_guard; lia ].
all: first [ destruct SEPS as [-> | [S1 S2]]; [left; reflexivity | right; split; lia]
| right; unfold zlength in BUFL |- *; split; lia ]. }
cbv beta. intros [] st' ms' PO.
destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
apply implM_upd. apply evt_done. rewrite ?get_set.
unfold stdout_writefn_post, so_after, stdout_cells, wfn_of, lbf_of, file_cells. rewrite FIRST. cbn [so_first so_buf so_lbf_nl].
sys_finish.
+ eapply munch_weaken; [| exact MU2]. unfold sub_fp, STDIO_WRITE_DEPTH, STDOUT_WRITE_DEPTH in *; cbn [outside]; intros; lia.
+ rewrite ?set_set. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End StdoutWrite.
