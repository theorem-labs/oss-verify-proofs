(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseAbs FseWriterRT FseNCountRT FseHarness.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Stdio_pure.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require Import PImg RF_fse_iface RF_fse_h_model RF_fse_h_fill.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require Startup_B.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common.FseWalkKit.simpl_arr_sizes_fwk_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Definition PC_B_ENTRY : Z := 0x13538.
Definition PC_B_EXIT_RA : Z := 0x1366c.
Definition PFUZZ_MALLOC_B : Z := 0x14408.
Definition OFF_NC : Z := 536.
Definition OFF_DATA : Z := 1048.
Definition phaseB_post (gp tp s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(SP P D : Z) (pl : list Z) (lo : Z) (m : fmem) : machine_state -> Prop :=
fun ms' => exists tl msv nc data dsz bsz rem buf' (junk16 jtl rtjunk : list byte)
(t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 t3 t4 t5 t6 : word) (m' : fmem),
fseA pl (zlen pl) = (tl, msv, nc, data, dsz, bsz, rem)
/\ ms' = MS (mkR (Z_to_bv 64 PC_B_EXIT_RA) (Z_to_bv 64 SP) gp tp t0 t1 t2 (Z_to_bv 64 P) (Z_to_bv 64 msv)
(Z_to_bv 64 bsz) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 tl) s3 (Z_to_bv 64 dsz) (Z_to_bv 64 bsz) s6 s7
s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PFUZZ_MALLOC_B) fc None m' (seg_rom psegs)
/\ munch [(P + 8, P + 16); (SP - 80, SP + 1560)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
/\ stk psegs m' lo SP
/\ prod_at m' P D rem
/\ rw_cells psegs m' SP [CB 16 junk16; CB 4 jtl; C4 (Z_to_bv 64 255); CB 512 rtjunk]
/\ u8arr psegs m' (SP + OFF_NC) (u16s (map (Z_to_bv 64) nc))
/\ u8arr psegs m' (SP + OFF_DATA) (map (Z_to_bv 8) buf')
/\ length buf' = 512%nat /\ firstn (Z.to_nat dsz) buf' = data.
Lemma rw0_val : forall tl, 5 <= tl <= 12 ->
Z.lxor (bv_swrap 32 (Z.shiftl 18446744073709551615 (tl mod 32)) mod 18446744073709551616) 18446744073709551615 = 2^tl - 1.
Proof.
intros tl H.
Local Ltac2 Set LiaHints.tbl := fun () => "0010=44315663753.2000003S1H".
assert (C : tl = 5 \/ tl = 6 \/ tl = 7 \/ tl = 8 \/ tl = 9 \/ tl = 10 \/ tl = 11 \/ tl = 12) by lia.
destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma rw0_val' : forall tl, 5 <= tl <= 12 ->
Z.lxor (Z.land (bv_swrap 32 (Z.shiftl 18446744073709551615 (tl mod 32))) 18446744073709551615) 18446744073709551615 = 2^tl - 1.
Proof.
intros tl H.
Local Ltac2 Set LiaHints.tbl := fun () => "0010=44315663753.2000003S1H".
assert (C : tl = 5 \/ tl = 6 \/ tl = 7 \/ tl = 8 \/ tl = 9 \/ tl = 10 \/ tl = 11 \/ tl = 12) by lia.
destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma land_ones32 : forall x, 0 <= x < 4294967296 -> Z.land x 4294967295 = x.
Proof. intros x Hx. change 4294967295 with (Z.ones 32). Local Ltac2 Set LiaHints.tbl := fun () => "0020=44015171046.253487459491.2000001005SS2Hx".
rewrite Z.land_ones by lia. apply Z.mod_small. change (2^32) with 4294967296. lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma shl48_land : forall x, 0 <= x < 65536 -> Z.land (Z.shiftl x 48) 18446744073709551615 = x * 281474976710656.
Proof.
intros x Hx. change 18446744073709551615 with (Z.ones 64). Local Ltac2 Set LiaHints.tbl := fun () => "0030=19536701855.222538140902.235497640934.2000004005006S2HxSS".
rewrite Z.land_ones by lia. rewrite Z.shiftl_mul_pow2 by lia.
change (2^48) with 281474976710656. change (2^64) with 18446744073709551616. apply Z.mod_small. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section PhaseB.
Hypothesis U32R : prod_u32r_stmt.
Hypothesis I32R : prod_i32r_stmt.
Hypothesis WBOUND : fse_wbound_stmt.
Hypothesis WRITE : fse_write_stmt.
Hypothesis ISERR : fse_iserror_stmt.
#[using="U32R WBOUND WRITE ISERR"] Lemma phaseB3 :
forall (gp tp s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m m1 : fmem) (SP P D : Z) (pl : list Z) (lo : Z)
(tl msv r4 bsz r5 : Z) (nc : list Z) (j16 j4a j4b jrt jdata : list byte)
(x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word),
uint32Range pl r4 (hdrSize nc msv tl) 512 = (bsz, r5) ->
fseA pl (zlen pl) = (tl, msv, nc, fse_data nc msv tl, hdrSize nc msv tl, bsz, r5) ->
0 <= r4 <= zlen pl ->
Forall (fun c => 0 <= c < 256) pl ->
u8arr psegs m1 (SP + 536) (u16s (map (Z_to_bv 64) nc)) ->
rw_cells psegs m1 P [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 r4)] ->
bytes_at psegs m1 D (map (Z_to_bv 8) pl) ->
rw_cells psegs m1 SP [CB 16 j16; CB 4 j4a; CB 4 j4b; CB 512 jrt] ->
rw_cells psegs m1 (SP + 1048) [CB 512 jdata] ->
stk psegs m1 lo SP -> lo <= SP - 80 -> 0 <= SP -> SP + 1632 < 2^64 ->
P + 16 <= lo -> D + zlen pl <= lo -> (D + zlen pl <= P \/ P + 16 <= D) -> 0 < P -> P mod 8 = 0 -> 0 < D -> SP mod 16 = 0 ->
munch [(P + 8, P + 16); (SP - 80, SP + 1560)] m m1 -> wmono psegs m m1 -> mem_inv psegs m1 ->
evt psegs (phaseB_post gp tp s8 s9 s10 s11 F fc SP P D pl lo m)
(MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 msv) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 tl) x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x1360c) fc None m1 (seg_rom psegs)).
Proof.
intros until x31. intros EB EA R4 PLB NCA PR PAY FRLO DATAC ST LO SP0 SPH PLO DLO DP P0 PAL D0 SPAL MU WM MI.
assert (LENP : zlen (map (Z_to_bv 8) pl) = zlen pl) by (rewrite length_map; reflexivity).
assert (AB : all_bytes pl) by (apply Forall_all_bytes; exact PLB).
Local Ltac2 Set LiaHints.tbl := fun () => "0130?11158547152.88 11418861417.12511467584293.10312428150072.12112428150072.13712904212107.12213852647685.14615718194651.12215718194651.13816603128996.11916747972023.12216747972023.1381946522126.137 19957160977.11719962924073.12823442460715.11723488382379.94 23490659993.77 24583271506.10324984467862.13325071629079.12525076071819.12125076071819.12225076071819.13725177572496.1382599566312.146 26166611579.91 26489700490.1032724359532.125 28555575282.89 29542820569.13330035529559.10330035720224.11931992077787.12231992077787.1383573547238.125 38452838840.11738542783228.11938551223786.11740316657281.11740813119656.12143164648726.11744363233235.11744732751703.12545178983888.89 46662182217.10347044310243.10347797046682.10350367033113.10350806104399.11751613418308.10352743870263.10355257533477.14056300254992.88 57622410744.12257622410744.13859314923118.11859314923118.91 61816609716.1036261130714.117 6271809577.119 63102239738.89 63940103961.10366946053710.12568359421783.125757919991.146  9668885428.103 00000;00W00X00Y00Z00[00\01801^02=02l03^04>04]05<05X05k06006S06o07K07j07k08Q08R08n09=09\0:<0:G0;10;Q0<10<[0<\0=B0=a0>@0>\0?80?T0@00@O0@k0A60AZ0B=0BY0C50CT0CU0D40D^0Di0EU0F30FQ0F^0G:0GY0H80H@0H\0IB0I^0JD0J`S3SP02F22F4S3SP02F42DB3LJD3LD03WN24LMNCFFFFFS3SP02F42DB3LJD3LD03WN24LMNCS2LO3SP03PLO2P02F42DB3LJD3LD03WN24LMNCS3SP02F42F62DB3LJD3LD03WN24LMNCS2LO3SP03DLO2P04LENP2F42DB3LJD3LD03WN24LMNC3FWSS2LO3SP03PLO3DLO2DP2P04LENP2F42DB3LJD3LD03WN24LMNCS3SP03PLO2F42DB3LJD3LD03WN24LMNCS3SP02F42F62DB3LJD3LD03WN24LMNCS3SP02F42F62DB3LJD3LD03WN24LMNCS3SP02F42DB3LJD3LD03WN24LMNCS3SP02F42DB3LJD3LD0S3SP0S3SP03SPH2P02F42DB3LJD3LD03WN24LMNCS3SP02F42DB3LJD3LD03WN24LMNCS3SP02F42DB3LJD3LD03WN24LMNCS3SP02P02F42DB3LJD3LD03WN24LMNCFS2LO3SP03PLO2P02F42DB3LJD3LD03WN24LMNCFS3SP02F42DB3LJD3LD03WN24LMNCS3SP02F42F73WB0S3SP02P02F42DB3LJD3LD03WN24LMNCS3SP03SPH2F42DB3LJD3LD03WN24LMNCS3SP02F12F4S3SP02P02F42F63F112DB3LJD3LD03WN24LMNC3S5aS3SP03SPH2F42DB3LJD3LD03WN24LMNCS3SP03SPH2F42DB3LJD3LD03WN24LMNCS2LO3SP03PLO2P02F42DB3LJD3LD03WN24LMNC3FWSFS2LO3SP03DLO2P02F42DB3LJD3LD03WN24LMNCS3SP02F42F62DB3LJD3LD03WN24LMNCS2LO3SP02F42DB3LJD3LD03WN24LMNCS3SP02F42DB3LJD3LD03WN24LMNCS3SP02F42DB3LJD3LD03WN24LMNCS3SP02F42DB3LJD3LD03WN24LMNCS3SP02F42DB3LJD3LD03WN24LMNCS2R43SP02F42DB3LJD3LD03WN24LMNCS3SP02F42DB3LJD3LD03WN24LMNCS3SP02F22F4S3SP02P04SPAL2F42DB3LJD3LD03WN24LMNCS3SP03SPH2P02F42DB3LJD3LD03WN24LMNCS3SP02F42DB3LJD3LD03WN24LMNCS3SP02F42DB3LJD3LD03WN24LMNCS3SP02F42F62DB3LJD3LD03WN24LMNCFS3SP02F12F42DB3LJD3LD03WN24LMNCS3SP02P02F42F63F112DB3LJD3LD03WN24LMNC3S5aS3SP02F12F4S2LO3SP03PLO2P02F42DB3LJD3LD03WN24LMNC3FWS1HS3SP02F42DB3LJD3LD03WN24LMNC1HS3SP02F42DB3LJD3LD03WN24LMNC1KS3SP02F42F71KS3SP02F42DB3LJD3LD03WN24LMNCS3SP02F42F62DB3LJD3LD03WN24LMNCS3SP02F42F62DB3LJD3LD03WN24LMNCS3SP02F4S3SP02F42DB3LJD3LD03WN24LMNCS2LO3SP03PLO2P02F42DB3LJD3LD03WN24LMNCS3SP02F42DB3LJD3LD03WN24LMNCS3SP02P02F42F62DB3LJD3LD03WN24LMNC3S5aS3SP02F42DB3LJD3LD03WN24LMNC".
pose proof (fseA_facts pl (zlen pl) AB ltac:(lia)) as FACTS. rewrite EA in FACTS.
destruct FACTS as (F1 & F2 & V & F4 & _ & F6 & F7 & _ & F9 & F10 & F11 & F12).
unfold FSE_MIN_TABLELOG, FSE_MAX_TABLELOG in *.
set (dsz := hdrSize nc msv tl) in *.
zstep. zstep. zstep.
unfold fse_wbound_stmt, PFSE_WBOUND in WBOUND.
call_pure (WBOUND _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ msv tl); [lia| lia| reflexivity| reflexivity|].
pose proof (write_bound_nonneg msv tl ltac:(lia) ltac:(lia)) as WB0.
zstep. zstep.
if_cases K; zify_cond K; [exfalso; lia|]. clear K.
zstep. zstep. zstep. zstep. zstep. zstep.
pose proof (rw_cells_bound _ _ _ _ DATAC) as DB. cbn [cells_size csize Nat.add] in DB.
assert (LJD : length jdata = 512%nat) by (destruct DATAC as [[[Hn _] _] _]; exact Hn).
apply u8arr_of_rw_cells in DATAC. rewrite <- (bytes_of_unsigned jdata) in DATAC.
set (data0 := map bv_unsigned jdata) in *.
assert (LD0 : length data0 = 512%nat) by (subst data0; rewrite length_map; exact LJD).
pose proof (fseA_write_ncount pl (zlen pl) data0 AB ltac:(lia) LD0) as WN. rewrite EA in WN.
destruct WN as (buf' & WN1 & WN2 & WN3 & WN4 & WN5). fold dsz in WN1, WN3, WN4, WN5.
pose proof (valid_ncount_short _ _ _ V) as NCS.
assert (LMNC : length (map (Z_to_bv 64) nc) = 256%nat) by (rewrite length_map; exact F4).
assert (FWS : FSE_WRITE_STACK = 80) by reflexivity.
unfold fse_write_stmt, PFSE_WRITE in WRITE.
call (WRITE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SP (SP + 1048) (SP + 536) data0 buf' nc msv tl dsz lo);
[ first [ exact (proj1 NCA) | assumption | subst data0; apply bytes_unsigned_range | reflexivity | lia | rewrite LD0; lia | rewrite LD0; reflexivity
| right; lia | left; rewrite F4; lia | rewrite F4; lia | Z.div_mod_to_equations; lia ] .. | ].
rename POST into DATAA. rename PC into ST. rename MI0 into MI.
zstep. zstep.
unfold fse_iserror_stmt, PFSE_ISERROR in ISERR.
call_pure (ISERR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dsz); [lia| reflexivity|].
replace (2^64 - 119 <=? dsz) with false by (symmetry; apply Z.leb_gt; lia). cbn [Z.b2z].
zstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
zstep. zstep. zstep.
replace (dsz + 0) with dsz by lia. rewrite swrap32_small by lia.
zstep. zstep. zstep.
pose proof (uint32Range_spec pl r4 dsz 512 AB ltac:(lia) ltac:(lia) ltac:(change (2^32) with 4294967296; lia)) as S5.
rewrite EB in S5. destruct S5 as (S5a & S5b & _).
unfold prod_u32r_stmt, PPROD_U32R in U32R.
call (U32R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SP P D pl r4 dsz 512 lo);
[ first [ assumption | split; assumption | reflexivity | lia | change (2^31) with 2147483648; lia | change (2^24) with 16777216; lia ] .. | ].
rewrite EB in *. cbn [fst snd] in *.
rename POST into PR. rename PC into ST. rename MI0 into MI.
zstep. zstep.
rewrite land_ones32 by lia.
zstep. zstep.
apply evt_done. unfold phaseB_post.
exists tl, msv, nc, (fse_data nc msv tl), dsz, bsz, r5, buf', j16, j4a, jrt.
do 18 eexists.
split; [exact EA|]. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact PR|].
split; [exact FRLO|]. split; [exact NCA|]. split; [exact DATAA|]. split; [exact WN2| exact WN3].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="U32R WBOUND WRITE ISERR"] Lemma phaseB2 :
forall (gp tp s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m m1 : fmem) (SP P D : Z) (pl : list Z) (lo : Z)
(tl msv rw r3 v' r4 bsz r5 : Z) (pre : list Z) (j16 j4a j4b jrt jdata : list byte)
(x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31 : word),
let nc := Zupd msv v' (pre ++ repeat 0 (256 - length pre)) in
(rw = 0 -> exists c, uint32Range pl r3 0 1 = (c, r4) /\ v' = (if c =? 1 then -1 else rw + 1)) ->
(rw <> 0 -> v' = rw + 1 /\ r4 = r3) ->
uint32Range pl r4 (hdrSize nc msv tl) 512 = (bsz, r5) ->
fseA pl (zlen pl) = (tl, msv, nc, fse_data nc msv tl, hdrSize nc msv tl, bsz, r5) ->
0 <= rw <= 4095 -> 0 <= r3 <= zlen pl ->
Forall (fun c => 0 <= c < 256) pl ->
u8arr psegs m1 (SP + 536) (nc_arr pre) ->
rw_cells psegs m1 P [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 r3)] ->
bytes_at psegs m1 D (map (Z_to_bv 8) pl) ->
rw_cells psegs m1 SP [CB 16 j16; CB 4 j4a; CB 4 j4b; CB 512 jrt] ->
rw_cells psegs m1 (SP + 1048) [CB 512 jdata] ->
stk psegs m1 lo SP -> lo <= SP - 80 -> 0 <= SP -> SP + 1632 < 2^64 ->
P + 16 <= lo -> D + zlen pl <= lo -> (D + zlen pl <= P \/ P + 16 <= D) -> 0 < P -> P mod 8 = 0 -> 0 < D -> SP mod 16 = 0 ->
munch [(P + 8, P + 16); (SP - 80, SP + 1560)] m m1 -> wmono psegs m m1 -> mem_inv psegs m1 ->
evt psegs (phaseB_post gp tp s8 s9 s10 s11 F fc SP P D pl lo m)
(MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 msv) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 tl) (Z_to_bv 64 rw) (Z_to_bv 64 (SP + 536)) (Z_to_bv 64 msv) x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x135d4) fc None m1 (seg_rom psegs)).
Proof.
intros until x31. intros nc EC0 EC1 EB EA RW R3 PLB NCA PR PAY FRLO DATAC ST LO SP0 SPH PLO DLO DP P0 PAL D0 SPAL MU WM MI.
assert (LENP : zlen (map (Z_to_bv 8) pl) = zlen pl) by (rewrite length_map; reflexivity).
assert (AB : all_bytes pl) by (apply Forall_all_bytes; exact PLB).
Local Ltac2 Set LiaHints.tbl := fun () => "00a0?11455667281.99 11757049097.10111758986493.99 12428150072.11915718194651.12016747972023.1201946522126.119 20274448857.11623490659993.81 24445917831.95 25075775149.11625075775149.95 25076071819.11925076071819.12025177572496.12026261676838.10430035720480.10131710869459.11631710869459.95 31715861737.11631715861737.95 31716172017.94 31718270678.11531992077787.12033826578434.11633826578434.95 372471762.115  384941430.96   38542783484.10138754790695.11638754790695.95 40999532346.11640999532346.95 49700776872.11649700776872.95 52151158294.11554457662204.99 55345847492.11655573486431.11555577764831.11656458628970.95 57622410744.12058601235876.95 66714902530.11666714902530.95 6753751067.94  7049939919.94  7612119638.100 8575957466.95  00000D00U00f00g01B01i02>02?02D02E02h03F03a04<04=04Q04f05I05g06@06T06h07A07B07e08C08D08E08Y09509L09o0:M0:m0;H0;Y0;j0<?0<_0=:0=S0=f0><0>X0>o0?@0?Q0?e0@9S2R33SP02F44LNC03LWSS3SP02F44LNC03LWSS3SP02F44LNC03LWSFS2LO3SP03PLO2P02F44LNC03LWSS2LO3SP03PLO3DLO2DP2P04LENP2F44LNC03LWSS3SP03PLO2F44LNC03LWSFS3SP0FS2LO3SP03PLO2P02F22F44LNC03LWS4LWS2S2LO3SP03PLO2P02F22F44LNC03LWSS2LO3SP03PLO2P02F44LNC03LWSS2LO3SP03PLO2P02F44LNC03LWSFS2RW3SP02F44LNC03LWSS3SP03SPH2F44LNC03LWSS2LO3SP03PLO2P02F22F44LNC03LWS4LWS2S2LO3SP03PLO2P02F22F44LNC03LWSS3SP02F22F44LNC03LWS4LWS2S3SP02F22F44LNC03LWSS3SP02F22F44LNC03LWSS3SP02F22F44LNC03LWS4LWS2FS2LO3SP03PLO2P02F22F44LNC03LWS4LWS2S2LO3SP03PLO2P02F22F44LNC03LWSFFS2LO3SP02F44LNC03LWSS3SP02P02F22F44LNC03LWS4LWS2S3SP02P02F22F44LNC03LWSS2LO3SP03DLO2P02F22F44LNC03LWS4LWS2S2LO3SP03DLO2P02F22F44LNC03LWSS3SP03SPH2P02F22F44LNC03LWS4LWS2S3SP03SPH2P02F22F44LNC03LWSS3SP02F44LNC03LWSS3SP02F44LNC03LWSS3SP02F44LNC03LWS3S3aS2R33SP02P02F44LNC03LWS3S3b4LWS2S2R33SP02P02F44LNC03LWS3S3bS2RW3SP02P02F44LNC03LWS1KS3SP02F44LNC03LWS1HS3SP02P02F44LNC03LWS1KS3SP02P02F22F44LNC03LWS4LWS2S3SP02P02F22F44LNC03LWSS3SP02F44LNC03LWSS3SP02F44LNC03LWSS3SP02F22F44LNC03LWSS2RW3SP02F44LNC03LWS".
pose proof (fseA_facts pl (zlen pl) AB ltac:(lia)) as FACTS. rewrite EA in FACTS.
destruct FACTS as (F1 & F2 & V & F4 & _ & F6 & F7 & _ & F9 & F10 & F11 & F12).
unfold FSE_MIN_TABLELOG, FSE_MAX_TABLELOG in *.
unfold nc_arr in NCA.
set (nc0 := pre ++ repeat 0 (256 - length pre)) in *.
assert (LNC0 : length nc0 = 256%nat).
{ assert (length nc = 256%nat) by exact F4. subst nc. unfold Zupd in H. rewrite upd_nat_length in H. exact H. }
assert (LWS : length (map (Z_to_bv 64) nc0) = 256%nat) by (rewrite length_map; exact LNC0).
zstep. zstep. zstep. zstep.
rewrite (Z.shiftl_mul_pow2 msv 1) by lia. change (2^1) with 2. replace (msv * 2) with (2 * msv) by lia.
pose proof (u16arr_store_ok psegs _ (SP + 536) _ msv (wa (SP + 536 + 2 * msv)) NCA ltac:(rewrite LWS; lia) eq_refl) as SOK.
zstep.
pose proof (u16arr_write psegs _ (SP + 536) _ msv (Z_to_bv 64 (rw + 1)) NCA ltac:(rewrite LWS; lia)) as NCA2.
clear NCA. store_done.
rewrite upd_map_upd_nat in NCA2. fold (Zupd msv (rw + 1) nc0) in NCA2.
zstep.
rename NCA2 into NCA.
if_cases K; zify_cond K.
-
rewrite shl48_land in K by lia. assert (RWN : rw <> 0) by lia.
destruct (EC1 RWN) as [EV ER4]. subst r4.
eapply (phaseB3 gp tp s8 s9 s10 s11 F fc m m0 SP P D pl lo tl msv r3 bsz r5 nc); try eassumption; try lia.
subst nc. rewrite EV. exact NCA.
- rewrite shl48_land in K by lia. assert (RWZ : rw = 0) by lia.
destruct (EC0 RWZ) as (c & ECc & EV).
pose proof (uint32Range_spec pl r3 0 1 AB ltac:(lia) ltac:(lia) ltac:(change (2^32) with 4294967296; lia)) as S3.
rewrite ECc in S3. destruct S3 as (S3a & S3b & _).
zstep. zstep. zstep. zstep. zstep.
unfold prod_u32r_stmt, PPROD_U32R in U32R.
call (U32R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SP P D pl r3 0 1 lo);
[ first [ assumption | split; assumption | reflexivity | lia | change (2^31) with 2147483648; lia | change (2^24) with 16777216; lia ] .. | ].
rewrite ECc in *. cbn [fst snd] in *.
rename POST into PR. rename PC into ST. rename MI0 into MI. unfold prod_at in PR.
zstep. if_cases K2; zify_cond K2.
+
eapply (phaseB3 gp tp s8 s9 s10 s11 F fc m _ SP P D pl lo tl msv r4 bsz r5 nc); try eassumption; try lia.
subst nc. rewrite EV. replace (c =? 1) with false by (symmetry; apply Z.eqb_neq; exact K2). exact NCA.
+
subst c.
assert (LWS2 : length (map (Z_to_bv 64) (Zupd msv (rw + 1) nc0)) = 256%nat)
by (rewrite length_map; unfold Zupd; rewrite upd_nat_length; exact LNC0).
zstep.
pose proof (u16arr_store_ok psegs _ (SP + 536) _ msv (wa (SP + 536 + 2 * msv)) NCA ltac:(rewrite LWS2; lia) eq_refl) as SOK.
zstep.
pose proof (u16arr_write psegs _ (SP + 536) _ msv (Z_to_bv 64 (-1)) NCA ltac:(rewrite LWS2; lia)) as NCA2.
clear NCA. store_done.
rewrite upd_map_upd_nat in NCA2. unfold Zupd in NCA2. rewrite upd_nat_idem in NCA2. fold (Zupd msv (-1) nc0) in NCA2.
eapply (phaseB3 gp tp s8 s9 s10 s11 F fc m _ SP P D pl lo tl msv r4 bsz r5 nc); try eassumption; try lia.
subst nc. rewrite EV. cbn [Z.eqb Pos.eqb]. exact NCA2.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="U32R I32R WBOUND WRITE ISERR"] Theorem phaseB_proof :
forall (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : fmem) (SP P D : Z) (pl : list Z) (lo : Z) (junk : list byte),
rw_cells psegs m SP [CB 1560 junk] ->
prod_at m P D (zlen pl) -> payload_at m D pl ->
stk psegs m lo SP -> lo <= SP - 80 -> 0 <= SP -> SP + 1632 < 2^64 ->
P + 16 <= lo -> D + zlen pl <= lo -> (D + zlen pl <= P \/ P + 16 <= D) ->
0 < P -> P mod 8 = 0 -> 0 < D -> SP mod 16 = 0 ->
mem_inv psegs m ->
evt psegs (phaseB_post gp tp s8 s9 s10 s11 F fc SP P D pl lo m)
(MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PC_B_ENTRY) fc None m (seg_rom psegs)).
Proof.
intros until junk. intros FR PR PL ST LO SP0 SPH PLO DLO DP P0 PAL D0 SPAL MI.
destruct PL as [PAY PLB].
assert (LENP : zlen (map (Z_to_bv 8) pl) = zlen pl) by (rewrite length_map; reflexivity).
assert (AB : all_bytes pl) by (apply Forall_all_bytes; exact PLB).
destruct (fseA_unfold pl (zlen pl)) as (tl & r1 & msv & r2 & pre & rw & r3 & v' & r4 & bsz & r5 & E1 & E2 & E3 & EC0 & EC1 & EB).
cbv zeta in EB. destruct EB as [EB EA].
set (nc := Zupd msv v' (pre ++ repeat 0 (256 - length pre))) in *.
Local Ltac2 Set LiaHints.tbl := fun () => "01>0?10105082325.14710300527061.14610698741345.14211801586693.14712428150072.11312428150072.12913414043285.14714258731668.94 14258783400.95 14289303062.14214939502105.13615047326888.14215550668838.95 15718194651.11315718194651.12916186709130.12816747972023.11416747972023.1301830867580.150 1946522126.113 1946522126.129 19646426257.15022700267513.14823490363412.94 23490594328.80 2420686483.150 25177572496.11425177572496.1302599566312.155 26492302758.17227235809680.15027242066989.14727367095973.15527721971957.94 28575982988.17430031381839.15030037817969.95 30037818096.11131992077787.11431992077787.13032239311345.1473516806137.111 3516842969.110 35693770006.11037934716299.14737942290214.15137945104438.15037945121459.12637949348897.14238544879660.11138544879789.95 39594055432.15040087687755.11040517252183.17241156022005.12541415857004.1254178179176.128 4288333238.142 44484923210.14645166859163.15545456959716.12546391977622.17247813955705.12855142473048.11056285484437.15057011364998.15057018323083.12857622410744.11457622410744.13059308628433.15159851873173.13259860646032.15162760376726.12563111278787.15064403764972.12567187188786.1287606134511.150 7612119637.149 00000E00M00X00`00a00b00c00k01301;01<01D01L01a02602>02_03@03Q03]03i04504?04G04L04[04\04]04e05>05Z06806906A06T06d07007<07=07>07X07`07h08008@08N08^08h09409?09J09Y09d0:D0:O0:W0:c0:n0;60;A0;L0;e0;m0<50<E0<T0<\0<f0=00=B0=M0=\0=d0>50>@0>H0>W0>bS2LO3SP03PLO2P02F12F4S3SP02F4S3SP02F22F4S3SP02F4FFFS3SP02F4S3SP02F4S3SP02F4FS3SP02F4S3SP02F4S2LO3SP03PLO2P02F12F4S2LO3SP03PLO2P02F12F4S3SP02F4S2LO3SP03PLO3DLO2DP2P04LENP2F12F4S2LO3SP03PLO3DLO2DP2P04LENP2F12F4S3SP02F22F43FI21KS3SP03PLO2F4S3SP03PLO2F4S3SP02F43FI2S3SP02F41HS3SP02F4S3SP0S2LO3SP02F43FI2FFS3SP02F4S2LO3SP03PLO2P02F12F43FI2S3SP02P02F12F42S12S23FI13FI2S3SP02P02F12F42S12S23FI13FI21KFS3SP02F4S3SP02F22F43FI21K1HS3SP03SPH2F43FI2S3SP03SPH2F4S3SP03SPH2F4FFS2LO3SP03DLO2P04LENP2F12F4S3SP02F4S3SP02F4S3SP02F4S3SP02F43RW03FI2S3SP02F43FI21KS3SP02F43RW03FI2S3SP02F41HS3SP02F43RW0S2LO3SP02F4S2LO3SP02F4S3SP02F22F43FI2S3SP02F42S1S3SP02P02F12F42S12S23FI13FI23FI6S3SP02F12F4S3SP02F4S3SP03SPH2F4S3SP02F42S2S3SP02F4S3SP02F22F4S3SP02F12F4S2LO3SP03PLO2P02F12F43FI2S3SP02F4S3SP02F4S3SP03SPH2F43FI2S3SP02F22F43FI2S3SP02F4S3SP02F41HS3SP02F41HS3SP02F12F43FI22K2S3SP02F12F4S3SP02F12F43FI2S3SP02F4S3SP02F22F43FI21KS3SP02F12F4S3SP02F4S3SP02F22F43FI2S3SP02F22F4".
pose proof (fseA_facts pl (zlen pl) AB ltac:(lia)) as FACTS. rewrite EA in FACTS.
destruct FACTS as (F1 & F2 & V & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12).
unfold FSE_MIN_TABLELOG, FSE_MAX_TABLELOG in *.
pose proof (munch_refl [(P + 8, P + 16); (SP - 80, SP + 1560)] m) as MU. pose proof (wmono_refl psegs m) as WM.
unfold PC_B_ENTRY. unfold prod_at in PR.
apply (rw_cells_split_CB _ _ _ [] _ _ _ [16; 4; 4; 512; 512; 512]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
zstep. zstep. zstep. zstep.
unfold prod_u32r_stmt, PPROD_U32R in U32R.
pose proof (uint32Range_spec pl (zlen pl) 5 12 AB ltac:(lia) ltac:(lia) ltac:(change (2^32) with 4294967296; lia)) as S1.
rewrite E1 in S1. destruct S1 as (_ & S1 & _).
call (U32R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SP P D pl (zlen pl) 5 12 lo);
[ first [ assumption | split; assumption | reflexivity | lia | change (2^31) with 2147483648; lia | change (2^24) with 16777216; lia ] .. | ].
rewrite E1 in *. cbn [fst snd] in *.
rename POST into PR. rename PC into ST. rename MI0 into MI. unfold prod_at in PR.
zstep. zstep. zstep. zstep. zstep.
pose proof (uint32Range_spec pl r1 0 255 AB ltac:(lia) ltac:(lia) ltac:(change (2^32) with 4294967296; lia)) as S2.
rewrite E2 in S2. destruct S2 as (_ & S2 & _).
call (U32R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SP P D pl r1 0 255 lo);
[ first [ assumption | split; assumption | reflexivity | lia | change (2^31) with 2147483648; lia | change (2^24) with 16777216; lia ] .. | ].
rewrite E2 in *. cbn [fst snd] in *.
rename POST into PR. rename PC into ST. rename MI0 into MI. unfold prod_at in PR.
zstep. zstep. zstep. zstep.
first [rewrite rw0_val by lia | rewrite rw0_val' by lia].
assert (RW0 : 0 < 2^tl - 1 <= 4095).
{ assert (2^5 <= 2^tl <= 2^12) by (split; apply Z.pow_le_mono_r; lia). change (2^5) with 32 in *. change (2^12) with 4096 in *. lia. }
zstep. zstep. zstep. zstep.
apply (proj1 (Stdio_pure.rw_cells_app _ _ _ [CB 16 _; CB 4 _; CB 4 _; CB 512 _] _)) in FR. destruct FR as [FRLO FRHI]. cbn [cells_size csize Nat.add] in FRHI.
apply (proj1 (Stdio_pure.rw_cells_app _ _ _ [CB 512 _] _)) in FRHI. destruct FRHI as [NCC DATAC]. cbn [cells_size csize Nat.add] in DATAC.
replace (SP + Z.of_nat 536) with (SP + 536) in NCC by lia.
replace (SP + Z.of_nat 536 + Z.of_nat 512) with (SP + 1048) in DATAC by lia.
zstep.
call (Startup_B.rmemset_specZ (SP + 536) 512 0); [exact NCC | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia |].
rename POST into NCZ. rename MI0 into MI. change (Z.to_nat 512) with 512%nat in NCZ.
apply u8arr_of_rw_cells in NCZ. change 512%nat with (2 * 256)%nat in NCZ. rewrite <- u16s_zero in NCZ.
zstep. zstep.
rewrite land_ones32 by lia.
pose proof (fse_fill_inv 256 pl r2 0 msv (2^tl - 1) [] pre rw r3 AB ltac:(lia) ltac:(lia) eq_refl ltac:(lia) ltac:(constructor) E3)
as (sF & FI1 & FI2 & FI3 & FI4 & FI5 & FI6).
zstep. if_cases K; zify_cond K.
-
assert (MSV0 : msv = 0) by lia.
rewrite (fse_fill_stop 256 pl r2 0 msv (2^tl - 1) []) in E3 by lia. injection E3 as <- <- <-.
replace (Z_to_bv 64 (2 ^ tl - 1)) with (Z_to_bv 64 (2 ^ tl - 1)) by reflexivity.
eapply (phaseB2 gp tp s8 s9 s10 s11 F fc m _ SP P D pl lo tl msv (2^tl - 1) r2 v' r4 bsz r5 []); try eassumption; try lia.
-
zstep. if_cases K2; zify_cond K2; [exfalso; lia|]. clear K2.
zstep. zstep.
replace (SP + 536) with (SP + 536 + 2 * 0) at 2 by lia. change (Z_to_bv 64 1) with (Z_to_bv 64 (0 + 1)).
eapply (fill_loop I32R gp tp s8 s9 s10 s11 F fc x42 SP P D (SP + 536) pl msv tl lo _
ltac:(lia) ltac:(lia) PLO DLO DP ltac:(lia) P0 PAL D0 ltac:(lia) 256%nat 0 (2^tl - 1) r2 []);
[ lia | lia | reflexivity | lia | exact PLB | lia | | ].
+
split; [exact NCZ|]. split; [exact PR|]. split; [exact PAY|]. split; [exact ST|].
split; [apply munch_refl|]. split; [apply wmono_refl| exact MI].
+
intros m2 pre' rwF r3' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y23 y28 y29 y30 y31 EF (NCA2 & PR2 & PAY2 & ST2 & MU2 & WM2 & MI2) RWF.
rewrite E3 in EF. injection EF as <- <- <-.
clear NCZ PR PAY ST MI.
transport_after_call psegs x42 m2 MU2 WM2.
eapply (phaseB2 gp tp s8 s9 s10 s11 F fc m m2 SP P D pl lo tl msv rw r3 v' r4 bsz r5 pre); try eassumption; try lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End PhaseB.
