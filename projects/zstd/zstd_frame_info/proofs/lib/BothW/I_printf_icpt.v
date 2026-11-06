(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import StrFun Stdio_pure.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ZBridge.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg RtCells ShadowTac F_irt F_rip F_tryinit I_printf_lib I_printf_common I_printf_formats.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

(* [comment removed for export] *)
Notation rt_ckpf m := (rw_cells bsegs m 0x132bb8 [C8 (Z_to_bv 64 4294967296)]).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma vfprintf_i_post : forall RNG x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (j16 : list byte) (rav s0v s1v s2v : word),
  mem_inv bsegs m ->
  rw_cells bsegs m (bv_unsigned sp) [CB 16 j16; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rng RNG (bv_unsigned sp) 48 ->
  evtF bsegs RNG (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc rav) fc None m (seg_rom bsegs))
    (MS (mkR x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44b74) fc None m (seg_rom bsegs)).
Proof.
  intros until s2v. intros MI FR RR. pose proof (rw_cells_bound _ _ _ _ FR) as B. cbn in B.
  do 6 zstep. apply evtF_done. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma vprintf_i_post : forall RNG x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (j24 : list byte) (rav s0v s1v : word),
  mem_inv bsegs m ->
  rw_cells bsegs m (bv_unsigned sp) [CB 24 j24; C8 s1v; C8 s0v; C8 rav] ->
  rng RNG (bv_unsigned sp) 48 ->
  evtF bsegs RNG (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc rav) fc None m (seg_rom bsegs))
    (MS (mkR x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44004) fc None m (seg_rom bsegs)).
Proof.
  intros until s1v. intros MI FR RR. pose proof (rw_cells_bound _ _ _ _ FR) as B. cbn in B.
  Local Ltac2 Set LiaHints.tbl := fun () => "0030>18161314178.5058579369012.44884536833.51  000003006009S1BS1BS1B".
do 5 zstep. apply evtF_done. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma fprintf_i_post : forall RNG x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (j32 : list byte) (va : list cell) (rav s0v s1v s2v : word),
  mem_inv bsegs m ->
  rw_cells bsegs m (bv_unsigned sp) ([CB 32 j32; C8 s2v; C8 s1v; C8 s0v; C8 rav] ++ va) -> cells_size va = 48%nat ->
  rng RNG (bv_unsigned sp) 112 ->
  evtF bsegs RNG (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 112)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc rav) fc None m (seg_rom bsegs))
    (MS (mkR x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44f90) fc None m (seg_rom bsegs)).
Proof.
  intros until s2v. intros MI FR SZ RR. pose proof (rw_cells_bound _ _ _ _ FR) as B.
  rewrite cells_size_app, SZ in B. cbn in B.
  apply (proj1 (rw_cells_app _ _ _ _ _)) in FR. destruct FR as [FR FRV].
  Local Ltac2 Set LiaHints.tbl := fun () => "0040>35918884660.4836331091331.5360294573698.548028185345.55 00000300600900<S1BS1BS1BS1B".
do 6 zstep. apply evtF_done. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
End CANSEC1.
Ltac iprem :=
  lazymatch goal with
  | |- evtF _ _ _ _ => idtac
  | |- mem_inv _ _ => first [assumption | eassumption]
  | |- context [bv_unsigned (Z_to_bv 64 _)] => rewrite !unsigned_lit by lia; iprem
  | |- stk _ _ _ _ => first [assumption | eassumption]
  | |- rw_cells _ _ _ _ => rewrite ?Z_to_bv_bv_unsigned; first [assumption | eassumption]
  | |- shadow_bytes _ _ _ _ => first [assumption | eassumption]
  | |- bytes_at _ _ _ _ => first [assumption | eassumption]
  | |- unpoisoned _ _ _ => first [assumption | eassumption]
  | |- wr_at _ _ _ _ => first [assumption | eassumption]
  | |- app_blk _ _ => first [assumption | eassumption]
  | |- Forall _ _ => first [assumption | eassumption]
  | |- _ = Z_to_bv 64 _ => first [reflexivity | assumption | symmetry; assumption]
  | |- rng _ _ _ => first [ assumption | match goal with H : rng _ _ _ |- _ => eapply rng_sub'; [exact H | unfold KHIGH, sf_hide in *; lia] end]
  | |- ?g => unfold KHIGH, sf_hide in *; first [assumption | lia]
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Definition fprintf_i_mid (ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 x13 x14 x15 x16 x17 t3 t4 t5 t6 m' j32,
    ms' = MS (mkR (Z_to_bv 64 0x44f90) (Z_to_bv 64 (bv_unsigned sp - 112)) gp tp t0 t1 t2
                  a1 a0 a0 a1 (Z_to_bv 64 (bv_unsigned sp - 48)) x13 x14 x15 x16 x17
                  (Z_to_bv 64 (bv_unsigned sp - 48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x8eb80) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2432, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp - 112)
    /\ rw_cells bsegs m' (bv_unsigned sp - 112)
         [CB 32 j32; C8 s2; C8 s1; C8 s0; C8 ra; C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7]
    /\ rt_inited m'.

Section FPRINTF.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (A n : Z).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2432)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis INI : rt_inited m.
  Hypothesis CKP : rt_ckpf m.
  Hypothesis RPF : rt_real_printf m.
  Hypothesis A1 : a1 = Z_to_bv 64 A.
  Hypothesis NA : (0 <= n /\ 65536 <= A - 64 /\ A + n + 64 < 2^47)%Z.
  Hypothesis FZ : shadow_bytes m (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0%Z).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RSHF : rng RNG (shad (A - 64)) (shad (A + n + 64) - shad (A - 64)).

  Notation MID := (fprintf_i_mid ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).

  (* [comment removed for export] *)
  #[using="MI ST LO KLO GOT SHB INI CKP RPF RI RSTK"] Lemma fprintf_i_A : forall Q,
    (forall m1 j8 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31,
       munch [(bv_unsigned sp + -2432, bv_unsigned sp)]%Z m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
       stk bsegs m1 lo (bv_unsigned sp + -112) ->
       rw_cells bsegs m1 (bv_unsigned sp + -112)
         [CB 8 j8; C8 (Z_to_bv 64 (bv_unsigned sp + -48)); C8 (Z_to_bv 64 (bv_unsigned sp + -48)); C8 (Z_to_bv 64 (bv_unsigned sp + -48));
          C8 s2; C8 s1; C8 s0; C8 ra; C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] ->
       rt_got m1 -> rt_shbase m1 -> rt_inited m1 -> rt_real_printf m1 ->
       evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 0x44f50) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 a1 a0
                              (Z_to_bv 64 0x1e9df) a1 (Z_to_bv 64 (bv_unsigned sp + -48)) x13 x14 x15 x16 x17
                              (Z_to_bv 64 (bv_unsigned sp + -48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x4403c) fc None m1 (seg_rom bsegs))) ->
    evtF bsegs RNG Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x44ed0) fc None m (seg_rom bsegs)).
  Proof.
    intros Q K.
    pose proof (munch_refl [(bv_unsigned sp + -2432, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold KHIGH in KLO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    Local Ltac2 Set LiaHints.tbl := fun () => "02c0?10263306008.82 11513985511.77 11799361125.11311799361125.79 11799361125.80 11799361125.81 11799361125.82 11799361125.96 11799489569.10811801586693.93 11972186776.81 12179673880.81 123561496.79   12776239640.79 13114317212.10813114317212.11013177566514.10413270676710.76 14023418560.80 14773250736.76 15026383640.81 15032830052.78 15151340440.80 15917186584.82 15957830552.81 18748625560.81 18887455772.79 19042827563.95 1968392128.79  20040839232.79 20090295662.10820210087832.80 20824881200.78 2115072284.76  21215643672.96 21250035837.93 21252132953.10821518274460.78 21600875239.77 22282192675.10822284289799.93 22328128792.82 23400781414.75 25122868580.78 26043030976.80 26817889712.79 27147338155.11227373230610.71 27373230610.86 2770259888.79  27718319512.81 27759887638.89 28072922155.81 29823858968.81 29852097692.77 3020683420.77  30924289048.81 3103202328.82  31161366443.80 32068840256.79 32869782320.78 32985609624.80 35303312792.81 35633624860.79 35784801432.80 3660504856.82  37321754422.75 37321754422.90 38061727256.79 38088095936.77 3825354776.82  38264599196.78 38880710680.82 38889038000.79 40810485912.80 4142759704.82  42367474456.81 43055122012.68 43121191467.81 43245169304.81 44123833920.79 44484923210.93 44487020398.10844821287320.11344873666096.77 45095562520.81 45580174360.96 45685315612.78 45685315612.93 45788200856.81 46386664472.96 46999964426.60 47287692011.10147382493616.78 48325856741.10948325856743.10748562591384.11348912292248.80 48945986456.81 49503149208.81 49632921830.76 49951849624.81 50033228952.81 50120722712.82 50125791591.77 50125791591.92 50141254592.80 50628435992.82 50664164139.78 5072571819.80  50753392792.11350925296560.78 51234361003.80 51384633319.77 51787079037.93 51789176153.10851843947621.10951843947623.92 52082184793.10852084281981.93 52151318827.81 52371274268.78 52448735896.81 52931482264.81 53150882660.78 53400667952.11053971039640.80 54002075495.77 54096612892.79 54292837656.82 54775059736.82 5496416704.79  55002379676.78 55238157483.79 55812115608.81 56143470912.78 56172315833.71 56172315833.86 56908737432.81 57052305983.71 57052305983.86 57507983000.11357956650648.11359308628304.1  59308628433.1  59308628566.1  59349455128.81 59452298416.93 59798679832.81 6014957611.80  60330452198.70 61026060568.96 62007962008.80 62160867008.94 62431484700.11062431484700.93 62697437406.10863851539480.82 63926788569.10863928885757.93 65045250584.81 65115206040.80 65212743211.80 65344174681.10865346271869.93 65436951088.77 67033122200.80 67089904920.82 67803480856.81 68196899904.11168394337816.79 6898299397.71  6898299397.86  7346986776.79  7987385664.78  8128395288.96  8603416747.79  8788598064.78  9969733400.82  00000800900:00;00<00=00>00?00D00I00Q00Y00a00i00j00k00l00m01101201:01;01C01K01S01[01\01a01e01i01j02202302402<02H02T02U02V02W02X02`02a02b02f02g02l02m02n02o03703803=03E03F03G03O03W03\03`03a03i04104204:04B04P04^04f04j05205305;05<05D05L05T05X05]05e05i05j05k06306406<06D06E06F06N06V06Z06[06\06]06^06f06n07607>07?07G07O07W07X07Y07]07e07j07o08708808=08>08J08V08W08X08d09009509609>09F09G09H09P09Q09R09Z09b09f09g09l0:40:80:90::0:B0:F0:J0:R0:Z0:^0:b0:f0:n0:o0;70;<0;=0;E0;M0;Q0;R0;S0;T0;\0;h0<40<<0<D0<I0<U0<a0<b0<j0=20=:0=>0=F0=G0=H0=P0=T0=\0=a0=b0=jS2LO3KLOSSSSSSSS3HspS3HspS2LO3KLOS2LO3KLOS2LO3KLOS2LO3KLOSSSSS2HBSS2LO3KLOSS2LO3KLOS2LO3KLOS2LO3KLOS2LO3KLOSS3SPRS2HBS2HBSS2LO3KLOSSS2LO3KLOS2LO3KLO3HspS2LO3KLO3HspSSFFS2LO3KLOSSS2HBSS3SPRFFSS2LO3KLOSS3SPRS2LO3KLOSSS2LO3KLOS2LO3KLOS3SPRS2HBSS2LO3KLOS2LO3KLOSS2LO3KLOS2LO3KLOS2LO3KLO3SPR1HS2LO3KLO3SPR1HS2LO3KLOS2HBS2LO3KLOSS2LO3KLOSS2LO3KLOS2LO3KLOS2LO3KLOS2LOS3SPRS2LO3KLOS2HBFFS2LO3KLOSS2LO3KLOS2LO3KLOSSS2LO3KLOS2LO3KLOS2LOSSSSS2LO3KLOS2LO3KLOS2LO3KLOS2LO3KLOSS2LO3KLOS2LO3KLOS2LO3KLOSSS2HBS2LO3KLOS3SPRS3SPRS2LO3KLOSS3SPRSS2LO3KLO3HspS2LO3KLO3HspSSS2LO3KLO3HspS2LO3KLO3HspS3SPRSS2LO3KLOS2LO3KLOSSS2LO3KLOSSS2LO3KLOS2LO3KLOS2HBSS3SPRS2LO3KLOS2HBSSS2LO3KLOS2LOS2LOS2LO3KLOS2LO3KLOS2K1S2K2S2K3S2LO3KLOSS2LO3KLOS3SPRSS2LO3KLOS2LO3KLOS2HBSSSS2LO3KLOS2LO3KLO3HspS2LO3KLO3HspS2LO3KLOS2LO3KLOS3SPRS2LO3KLO3HspS2LO3KLO3HspSS2LO3KLOS2LO3KLOS2LO3KLOS2HBS2LO3KLOFFS2LO3KLOS2HBS2LO3KLOS3SPRSS2LO3KLO".
assert (RSTK' : rng RNG (bv_unsigned sp + -2432) 2432) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof MI as MIc. pose proof ST as ST0. pose proof GOT as GOTc. pose proof SHB as SHBc. pose proof INI as INIc.
    pose proof CKP as CKPc. pose proof RPF as RPFc.
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in GOT;
    change (?P) with (sf_hide P) in SHB; change (?P) with (sf_hide P) in INI; change (?P) with (sf_hide P) in CKP;
    change (?P) with (sf_hide P) in RPF.
    recell CKPc 0%nat 1%nat [C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 1); CB 3 (repeat (Z_to_bv 8 0) 3)].
    carve_frame 112%nat ST0.
    do 15 zstep. zstep.
    call_sp tryinit_spec. all: match goal with |- ?g => idtac "=="; idtac g end. all: iprem.
    zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
    zstep. zstep. zstep.
    call_sp tryinit_spec. all: iprem.
    zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. cbv in K2. lia. } clear K2.
    do 3 zstep. zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. zstep. if_cases K3; zify_cond K3. { exfalso. clear -K3. cbv in K3. lia. } clear K3.
    do 4 zstep. zstep.
    eapply K; try assumption; eassumption.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  Hypothesis PCI : printf_common_int_stmt A n.

  #[using="A n MI ST LO KLO GOT SHB INI CKP RPF A1 NA FZ RI RSTK RSHF PCI"] Lemma fprintf_i_pre_int :
    evtF bsegs RNG MID (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x44ed0) fc None m (seg_rom bsegs)).
  Proof.
    apply fprintf_i_A. intros m1 j8 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 MU1 WM1 MI1 ST1 FR1 GOT1 SHB1 INI1 RPF1.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold KHIGH in KLO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    Local Ltac2 Set LiaHints.tbl := fun () => "00F0?11799456952.81 11801586693.10517222273888.98 18442817054.82 18540142809.11021250035837.10524897053686.10627375328819.82 31382798176.98 37321754422.86 37738370326.10144484923210.10546999964426.80 4917892871.105 51787079037.10551843947620.10556170217624.82 60318033760.98 62431484700.10663928885757.10565346271869.1056896203300.82  00000;00@00A00E00F00R00S00T00U00c00d00e00i00j01601701801901:01F01R01SS2LO3KLO2NAS3HspSS2LOSS2LO3KLO3HspSFSS2LO3KLO3SPR1HSFS2LOFS2LO3KLO3HspSSSSS2LO3KLO3HspS2LO3KLO3HspF".
assert (RSTK' : rng RNG (bv_unsigned sp + -2432) 2432) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (FZ1 : shadow_bytes m1 (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0%Z)).
    { eapply shadow_bytes_munch; [exact FZ | exact MU1 |]. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in GOT;
    change (?P) with (sf_hide P) in SHB; change (?P) with (sf_hide P) in INI; change (?P) with (sf_hide P) in CKP;
    change (?P) with (sf_hide P) in RPF; change (?P) with (sf_hide P) in FZ.
    call_sp PCI. all: iprem.
    do 4 zstep. do 3 zstep. zstep.
    apply evtF_done. unfold fprintf_i_mid.
    replace (bv_unsigned sp - 112)%Z with (bv_unsigned sp + -112)%Z by lia.
    replace (bv_unsigned sp - 48)%Z with (bv_unsigned sp + -48)%Z by lia.
    replace (bv_unsigned sp - 2432)%Z with (bv_unsigned sp + -2432)%Z by lia.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
      lazymatch goal with FR : rw_cells bsegs mf (bv_unsigned sp + -112) (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) |- _ =>
        pose proof (rw_cells_merge bsegs mf _ [] [c1; c2; c3; c4] rest FR) as FRm; cbn [app cells_size csize Nat.add] in FRm end end.
    do 14 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption. exact FRm.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  Variables (sstr : list byte) (RLO RHI : Z).
  Notation Sa := (bv_unsigned a2).
  Notation NS := (Z.of_nat (length sstr) + 1)%Z.
  Hypothesis LAY : rt_layout m.
  Hypothesis SSTR : bytes_at bsegs m Sa (sstr ++ [Z_to_bv 8 0]).
  Hypothesis SNOZ : Forall (fun b : byte => bv_unsigned b <> 0%Z) sstr.
  Hypothesis SEPS : (Sa + NS <= bv_unsigned sp - 2432 \/ bv_unsigned sp <= Sa)%Z.
  Hypothesis APPS : app_blk Sa (Sa + NS).
  Hypothesis SPOS : (0 < Sa)%Z.
  Hypothesis USTR : unpoisoned m Sa (Sa + NS).
  Hypothesis NSZ : (NS <= 2^40)%Z.
  Hypothesis R1 : (RLO <= Sa /\ Sa + NS <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z.
  Hypothesis WR1 : wr_at bsegs m (shad RLO) (shad RHI - shad RLO).
  Hypothesis RS : rng RNG Sa NS.
  Hypothesis RSH1 : rng RNG (shad RLO) (shad RHI - shad RLO).
  Hypothesis PCS : printf_common_s_stmt A n.

  #[using="A n MI ST LO KLO GOT SHB INI CKP RPF A1 NA FZ RI RSTK RSHF sstr RLO RHI LAY SSTR SNOZ SEPS APPS SPOS USTR NSZ R1 WR1 RS RSH1 PCS"] Lemma fprintf_i_pre_s :
    evtF bsegs RNG MID (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x44ed0) fc None m (seg_rom bsegs)).
  Proof.
    apply fprintf_i_A. intros m1 j8 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 MU1 WM1 MI1 ST1 FR1 GOT1 SHB1 INI1 RPF1.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold KHIGH in KLO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    Local Ltac2 Set LiaHints.tbl := fun () => "00V0?11799440546.10211801389858.10111801586693.12911803405368.99 14788810421.10614790997494.10917219881159.12018448874142.10618540142809.13221250035837.12921594911267.10924897053686.12827369286323.10627923144266.10631380405447.12037321754422.11037738370326.12538270114779.10538285077374.12144484923210.12946999964426.96 4917892871.129 51787079037.12951843947620.12756185189400.10659503987035.10659504015996.12260328355015.12060866711165.10662384499546.10062386236669.12962431484700.12863928885757.1296515440607.106 65346271869.1296611983004.109 68185727392.1066911148708.106 00000A00G00[00o01>01M01N01R01S01_01`01a01b01c01d02502602702802902=02>02J02K02L02M02N02O02U02`02l02m03903:03F03G03L03MS2LO3KLO4SEPS3AS'S4SEPSS2LO3KLO4SEPS2R13HspS2LO3KLO2NA4SEPS3AS'S2LO3KLO2R13SPRS2LO3KLO2R13SPRSS2LOSS2LO3KLO3HspSSFFSS2LO3KLO2R13SPR1HSSSFS2LOFS2LO3KLO3HspSSSSSS4SEPSS2LO3KLO2R1S2LO3KLO3HspSS2LO3KLO3HspFS2LO3KLO3HspFS3SPRF".
assert (RSTK' : rng RNG (bv_unsigned sp + -2432) 2432) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof APPS as APPS'. destruct APPS' as [LES AS']. unfold KLOW, KHIGH, KEND in AS'.
    assert (FZ1 : shadow_bytes m1 (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0%Z)).
    { eapply shadow_bytes_munch; [exact FZ | exact MU1 |]. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
    assert (LAY1 : rt_layout m1).
    { eapply rw_cells_transport; [exact LAY | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    assert (SSTR1 : bytes_at bsegs m1 Sa (sstr ++ [Z_to_bv 8 0])).
    { eapply bytes_at_transport; [exact SSTR | exact MU1 |]. rewrite length_app. cbn [length disjoint_from]. lia. }
    assert (USTR1 : unpoisoned m1 Sa (Sa + NS)).
    { eapply unpoisoned_munch; [exact USTR | exact MU1 |]. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
    assert (WR11 : wr_at bsegs m1 (shad RLO) (shad RHI - shad RLO)) by (eapply wr_at_transport; eassumption).
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in GOT;
    change (?P) with (sf_hide P) in SHB; change (?P) with (sf_hide P) in INI; change (?P) with (sf_hide P) in CKP;
    change (?P) with (sf_hide P) in RPF; change (?P) with (sf_hide P) in FZ; change (?P) with (sf_hide P) in LAY;
    change (?P) with (sf_hide P) in SSTR; change (?P) with (sf_hide P) in USTR; change (?P) with (sf_hide P) in WR1.
    chunk_split FR1 8%nat FRV. chunk_split FRV 1%nat FRW.
    call_sp PCS. all: iprem.
    chunk_join FRV FRW. chunk_join FR1 FRV.
    do 4 zstep. do 3 zstep. zstep.
    apply evtF_done. unfold fprintf_i_mid.
    replace (bv_unsigned sp - 112)%Z with (bv_unsigned sp + -112)%Z by lia.
    replace (bv_unsigned sp - 48)%Z with (bv_unsigned sp + -48)%Z by lia.
    replace (bv_unsigned sp - 2432)%Z with (bv_unsigned sp + -2432)%Z by lia.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
      lazymatch goal with FR : rw_cells bsegs mf (bv_unsigned sp + -112) (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) |- _ =>
        pose proof (rw_cells_merge bsegs mf _ [] [c1; c2; c3; c4] rest FR) as FRm; cbn [app cells_size csize Nat.add] in FRm end end.
    do 14 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption. exact FRm.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End FPRINTF.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition vprintf_i_mid (ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 x13 x14 x15 x16 x17 t3 t4 t5 t6 m' j24 j16,
    ms' = MS (mkR (Z_to_bv 64 0x44b74) (Z_to_bv 64 (bv_unsigned sp - 96)) gp tp t0 t1 t2
                  a0 (Z_to_bv 64 0x9d6d8) (Z_to_bv 64 0x9d6d8) a0 a1 x13 x14 x15 x16 x17
                  a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x8eb80) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2416, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp - 96)
    /\ rw_cells bsegs m' (bv_unsigned sp - 48) [CB 24 j24; C8 s1; C8 s0; C8 ra]
    /\ rw_cells bsegs m' (bv_unsigned sp - 96) [CB 16 j16; C8 s2; C8 a1; C8 a0; C8 (Z_to_bv 64 0x44004)]
    /\ rt_inited m'.

Section VPRINTF.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (A n : Z).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2416)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis INI : rt_inited m.
  Hypothesis CKP : rt_ckpf m.
  Hypothesis RPF : rt_real_printf m.
  Hypothesis A0 : a0 = Z_to_bv 64 A.
  Hypothesis NA : (0 <= n /\ 65536 <= A - 64 /\ A + n + 64 < 2^47)%Z.
  Hypothesis FZ : shadow_bytes m (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0%Z).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RSHF : rng RNG (shad (A - 64)) (shad (A + n + 64) - shad (A - 64)).
  Hypothesis PCI : printf_common_int_stmt A n.

  #[using="A n MI ST LO KLO GOT SHB INI CKP RPF A0 NA FZ RI RSTK RSHF PCI"] Lemma vprintf_i_pre :
    evtF bsegs RNG (vprintf_i_mid ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x43fa0) fc None m (seg_rom bsegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -2416, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold KHIGH in KLO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    Local Ltac2 Set LiaHints.tbl := fun () => "03H0?10263306008.11310263306008.79 11093997488.11011404882412.13111723034140.76 11799361125.11311799361125.11411799361125.11611799361125.13111799361125.79 11799361125.81 11799361125.82 11799361125.98 11799489569.10911799489569.14211799489570.12511801586693.92 11803324321.11811805421443.85 12037418212.77 13284814180.92 13284814186.94 14793086774.74 14793086774.90 15151340440.11415151340440.81 16475027684.11018540142809.14619042827563.11519042827563.81 19236734230.88 19340579248.95 19664730524.11120090295663.12620090295663.93 20667246060.13121215643672.11621215643672.82 21250035837.92 21252132953.10921252132953.14221252132954.12522282192672.12522284289799.92 22387597248.77 23077509607.13023139947184.11324897053686.14225042987031.13125393266480.79 25613863711.11925779550180.11026939498908.11126939498908.79 26939498908.95 27147338155.11327147338155.81 28072922155.11228072922155.78 28406852928.79 29158023216.11129323744831.70 29738897271.12629738897271.12829823858968.11429823858968.98 30085204460.13131377886384.79 31378308326.69 31384895300.13431704748700.11132802850098.10532907263168.11232985609624.11432985609624.81 34440526528.80 35142651312.11135784801432.11435784801432.81 35920075244.13136178739012.1343660504856.113 3660504856.79  37438167600.78 37821204774.1013825354776.113 3825354776.79  38908001203.1143946739303.109 40460011584.80 41194412848.1114142759704.113 4142759704.79  41873551410.11941873551411.86 41873552432.10341875649554.70 41897576499.11442250564406.10742250564406.12343055122012.67 43155708396.13143407189580.12943422820272.76 43678327964.78 44484923210.92 44487020397.12544487020398.10944487020398.14244821287320.11444821287320.82 44960421824.11445095562520.11445095562520.98 45580174360.11645580174360.82 46386664472.11646386664472.82 46462227904.96 46998232647.10347287692008.11847289789135.85 47349350067.11647561401098.59 47804764645.78 47804764650.11047804764650.94 47923310545.11148562591384.11448562591384.82 48793319857.1214915795747.109 4915795747.142 50148821093.78 50644243556.11050644243556.14150644243562.12750753392792.11450753392792.82 50977580352.11251787079037.92 51789176153.10951789176153.14251789176154.12552082184793.10952082184793.14252082184794.12552084281981.92 52277671964.11152277671964.12852277671964.14253087662514.13853710135069.10353971039640.11453971039640.81 54078018550.11155952418663.75 56003195754.11256170217624.86 56170217625.11956170218651.10356172315833.70 56980320960.11157405284894.86 57507983000.11457507983000.82 57956650648.11457956650648.82 58383961523.11359308628304.1  59308628433.1  59308628566.1  59308628695.1  59349455128.11459349455128.98 59510497308.93 59510497308.95 59798679832.11459798679832.98 60681498140.11061026060568.11661026060568.82 62065839047.12862697437407.12662697437407.93 62999281728.11263926788569.10963926788569.14263926788570.12563928885757.92 64043097572.12564043097578.12764284135708.11365045250584.11465045250584.98 65212743211.11365212743211.97 65344174681.10965344174681.14265344174682.12565346271869.92 67033122200.11467033122200.81 67210899763.1146896202279.103 6896203300.86  6896203301.119 6898299397.70  7495246620.79  7589930820.134 8128395288.116 8128395288.82  8603416747.113 8603416747.80  9969733400.113 9969733400.79  00000800@00A00I00J00K00L00M00N00O00P00Q00R00W00\00a00f01101<01=01>01?01M01[01c01k01l01m02202702802902:02;02<02D02L02T02`02l03803D03E03F03J03O03P03Q03R03S03W03X03Y03Z03[03`03e03j03o04304404804904:04B04J04R04S04T04U04V04W04[04c04k04o05005805@05H05I05Q05Y05Z05^05f05n05o06006406506=06E06F06G06H06I06J06X06f06j07207607707807907:07;07<07D07L07P07X07`07h08008808@08D08E08F08G08H08L08M08N08O08P08X08`08a08b08c08d08e08f08g08o09709;09G09S09_09k0:70:C0:O0:[0:\0:]0:^0:_0:c0:k0;30;40;50;60;70;80;90;:0;>0;B0;J0;R0;Z0;b0;c0;g0;k0;o0<30<;0<C0<D0<E0<M0<U0<V0<^0<f0<g0<h0<i0<m0=90=E0=Q0=]0=^0=_0=`0=h0>00>50>:0>F0>R0>^0>j0?20?:0?;0?<0?=0?>0??0?@0?A0?I0?Q0?V0?[0?c0?kS2LO3KLOS2LO3KLOSS2LO3KLOSSSSSSSSSS3HspS3HspS3HspS3HspS2LO3KLO2NAS2LO3KLO2NASSSS2LO3KLO3SPR1HS2LO3KLO3SPR1HS2LO3KLOS2LO3KLOSSS3SPRS3SPRSSSSSS2LO3KLOS2LO3KLOS2LO3KLOS2LO3KLO3HspS2LO3KLO3HspS2LO3KLO3HspS2LO3KLO3HspFFS2HBS3SPRSSSSS2LOSSSSS3SPRS3SPRS3SPRS3SPRS2HBSS2LOSSS2LO3KLOS2LO3KLOS2LO3KLOSSSSSS2HBS2LO3KLOS2LO3KLOS2HBSS2LO3KLOS2LO3KLOS2LO3KLOSS2LO3KLOS2LO3KLOSS2LOS2LO3KLOS2LO3KLOSSS2HBSS2LO3KLOS2LO3KLOFFFFSS2LO3KLO3SPR1HS2LO3KLO3SPR1HS2LOS2LO3KLOS2HBSSFFFFS2LO3KLOS2LO3KLOS2HBS2LO3KLOS2LO3KLOS2LO3KLOS2LO3KLOS2LO3KLOS2LO3KLOS2HBSSSSS2LOSSSSS2LO3KLOS2LO3KLOSFFSSSSS2LO3KLOS2LO3KLOS2HBS2LO3KLO3HspS2LO3KLO3HspS2LO3KLO3HspS2LO3KLO3HspS2LO3KLO3HspS2LO3KLO3HspS2LO3KLO3HspS2LO3KLO3HspSSSSS2LOS2LO3KLOS2LO3KLOSSSSSSSS2HBS2LOS2LO3KLOS2LO3KLOS2LO3KLOS2LO3KLOSS2K1S2K2S2K3S2K4S2LO3KLOS2LO3KLOSSS2LO3KLOS2LO3KLOSS2LO3KLOS2LO3KLOSSSS2HBS2LO3KLO3HspS2LO3KLO3HspS2LO3KLO3HspS2LO3KLO3HspSSSS2LO3KLOS2LO3KLOS3SPRS3SPRS2LO3KLO3HspS2LO3KLO3HspS2LO3KLO3HspS2LO3KLO3HspS2LO3KLOS2LO3KLOSFFFFSSS2LO3KLOS2LO3KLOS3SPRS3SPRS2LO3KLOS2LO3KLO".
assert (RSTK' : rng RNG (bv_unsigned sp + -2416) 2416) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof MI as MIc. pose proof ST as ST0. pose proof GOT as GOTc. pose proof SHB as SHBc. pose proof INI as INIc.
    pose proof CKP as CKPc. pose proof RPF as RPFc.
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in GOT;
    change (?P) with (sf_hide P) in SHB; change (?P) with (sf_hide P) in INI; change (?P) with (sf_hide P) in CKP;
    change (?P) with (sf_hide P) in RPF.
    recell CKPc 0%nat 1%nat [C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 1); CB 3 (repeat (Z_to_bv 8 0) 3)].
    carve_frame 48%nat ST0.
    do 7 zstep. zstep.
    call_sp tryinit_spec. all: iprem.
    zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
    do 3 zstep. zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. cbv in K2. lia. } clear K2.
    do 4 zstep. zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) => lazymatch goal with MU1 : munch _ m m1 |- _ =>
      assert (FZ1 : shadow_bytes m1 (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0%Z))
        by (eapply shadow_bytes_munch; [exact FZ | exact MU1 |]; cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia)
    end end.
    change (?P) with (sf_hide P) in FZ.
    call_sp PCI. all: iprem.
    clear FZ1.
    (* [comment removed for export] *)
    do 4 zstep. zstep.
    do 7 zstep. zstep.
    (* [comment removed for export] *)
    match goal with H : stk bsegs _ lo (bv_unsigned sp + -48) |- _ => carve_frame 48%nat H end.
    do 9 zstep. zstep.
    call_sp tryinit_spec. all: iprem.
    zstep. if_cases K3; zify_cond K3. { exfalso. clear -K3. cbv in K3. lia. } clear K3.
    do 3 zstep. zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. zstep. if_cases K4; zify_cond K4. { exfalso. clear -K4. cbv in K4. lia. } clear K4.
    do 4 zstep. zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) => lazymatch goal with MU1 : munch _ m m1 |- _ =>
      assert (FZ2 : shadow_bytes m1 (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0%Z))
        by (unfold sf_hide in FZ; eapply shadow_bytes_munch; [exact FZ | exact MU1 |]; cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia)
    end end.
    call_sp PCI. all: iprem.
    clear FZ2.
    do 5 zstep. zstep.
    apply evtF_done. unfold vprintf_i_mid.
    replace (bv_unsigned sp - 96)%Z with (bv_unsigned sp + -96)%Z by lia.
    replace (bv_unsigned sp - 48)%Z with (bv_unsigned sp + -48)%Z by lia.
    replace (bv_unsigned sp - 2416)%Z with (bv_unsigned sp + -2416)%Z by lia.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
      lazymatch goal with FRa : rw_cells bsegs mf (bv_unsigned sp + -48) (?c1 :: ?c2 :: ?c3 :: ?rest) |- _ =>
        pose proof (rw_cells_merge bsegs mf _ [] [c1; c2; c3] rest FRa) as FRm1; cbn [app cells_size csize Nat.add] in FRm1 end;
      lazymatch goal with FRb : rw_cells bsegs mf (bv_unsigned sp + -96) (?c1 :: ?c2 :: ?rest) |- _ =>
        pose proof (rw_cells_merge bsegs mf _ [] [c1; c2] rest FRb) as FRm2; cbn [app cells_size csize Nat.add] in FRm2 end end.
    do 15 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption. exact FRm1. exact FRm2.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End VPRINTF.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Corollary vprintf_i_pre_d : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2416)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> rt_inited m -> rt_ckpf m -> rt_real_printf m ->
  a0 = Z_to_bv 64 FMT_D ->
  shadow_bytes m (shad (FMT_D - 64)) (shad (FMT_D + 3 + 64)) (fun _ => 0%Z) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad (FMT_D - 64)) (shad (FMT_D + 3 + 64) - shad (FMT_D - 64)) ->
  evtF bsegs RNG (vprintf_i_mid ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x43fa0) fc None m (seg_rom bsegs)).
Proof. intros. eapply vprintf_i_pre; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast. { unfold FMT_D. Local Ltac2 Set LiaHints.tbl := fun () => "0010=2309797376.51000001S".
lia. } exact printf_common_d_stmt. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Corollary fprintf_i_pre_toobig : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2432)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> rt_inited m -> rt_ckpf m -> rt_real_printf m ->
  a1 = Z_to_bv 64 FMT_TOOBIG ->
  shadow_bytes m (shad (FMT_TOOBIG - 64)) (shad (FMT_TOOBIG + 32 + 64)) (fun _ => 0%Z) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad (FMT_TOOBIG - 64)) (shad (FMT_TOOBIG + 32 + 64) - shad (FMT_TOOBIG - 64)) ->
  evtF bsegs RNG (fprintf_i_mid ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44ed0) fc None m (seg_rom bsegs)).
Proof. intros. eapply fprintf_i_pre_int; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast. { unfold FMT_TOOBIG. Local Ltac2 Set LiaHints.tbl := fun () => "0010>68284883888.51000001S".
lia. } exact printf_common_toobig_stmt. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Definition fprintf_i_pre_s_stmt (A n : Z) : Prop :=
  forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (sstr : list byte) (RLO RHI : Z),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2432)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> rt_inited m -> rt_ckpf m -> rt_real_printf m -> rt_layout m ->
  a1 = Z_to_bv 64 A ->
  shadow_bytes m (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0%Z) ->
  bytes_at bsegs m (bv_unsigned a2) (sstr ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0%Z) sstr ->
  (bv_unsigned a2 + (Z.of_nat (length sstr) + 1) <= bv_unsigned sp - 2432 \/ bv_unsigned sp <= bv_unsigned a2)%Z ->
  app_blk (bv_unsigned a2) (bv_unsigned a2 + (Z.of_nat (length sstr) + 1)) -> (0 < bv_unsigned a2)%Z ->
  unpoisoned m (bv_unsigned a2) (bv_unsigned a2 + (Z.of_nat (length sstr) + 1)) -> (Z.of_nat (length sstr) + 1 <= 2^40)%Z ->
  (RLO <= bv_unsigned a2 /\ bv_unsigned a2 + (Z.of_nat (length sstr) + 1) <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z ->
  wr_at bsegs m (shad RLO) (shad RHI - shad RLO) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad (A - 64)) (shad (A + n + 64) - shad (A - 64)) ->
  rng RNG (bv_unsigned a2) (Z.of_nat (length sstr) + 1) -> rng RNG (shad RLO) (shad RHI - shad RLO) ->
  evtF bsegs RNG (fprintf_i_mid ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44ed0) fc None m (seg_rom bsegs)).

End CANSEC2.
Ltac fis PC A := unfold fprintf_i_pre_s_stmt; intros; eapply fprintf_i_pre_s; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; [unfold A; lia | exact PC].
Section CANSEC3. Context {rc : runConstT}.
#[using="Type"] Corollary fprintf_i_pre_usage : fprintf_i_pre_s_stmt FMT_USAGE 16. Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0010>32002469942.66000001S".
fis printf_common_usage_spec FMT_USAGE. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Corollary fprintf_i_pre_cantopen : fprintf_i_pre_s_stmt FMT_CANTOPEN 20. Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0010>45811522422.66000001S".
fis printf_common_cantopen_spec FMT_CANTOPEN. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Corollary fprintf_i_pre_readerr : fprintf_i_pre_s_stmt FMT_READERR 22. Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0010>66268284310.66000001S".
fis printf_common_readerr_spec FMT_READERR. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC3.
