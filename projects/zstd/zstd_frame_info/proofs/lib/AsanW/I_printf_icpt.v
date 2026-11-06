(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import StrFun Stdio_pure.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ZBridge.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg RtCells ShadowTac F_irt F_rip F_tryinit I_printf_lib I_printf_common I_printf_formats.
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
Notation rt_ckpf m := (rw_cells asegs m 0x1329f8 [C8 (Z_to_bv 64 4294967296)]).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma vfprintf_i_post : forall RNG x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (j16 : list byte) (rav s0v s1v s2v : word),
  mem_inv asegs m ->
  rw_cells asegs m (bv_unsigned sp) [CB 16 j16; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rng RNG (bv_unsigned sp) 48 ->
  evtF asegs RNG (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc rav) fc None m (seg_rom asegs))
    (MS (mkR x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44b70) fc None m (seg_rom asegs)).
Proof.
  intros until s2v. intros MI FR RR. pose proof (rw_cells_bound _ _ _ _ FR) as B. cbn in B.
  do 6 zstep. apply evtF_done. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma vprintf_i_post : forall RNG x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (j24 : list byte) (rav s0v s1v : word),
  mem_inv asegs m ->
  rw_cells asegs m (bv_unsigned sp) [CB 24 j24; C8 s1v; C8 s0v; C8 rav] ->
  rng RNG (bv_unsigned sp) 48 ->
  evtF asegs RNG (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc rav) fc None m (seg_rom asegs))
    (MS (mkR x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44000) fc None m (seg_rom asegs)).
Proof.
  intros until s1v. intros MI FR RR. pose proof (rw_cells_bound _ _ _ _ FR) as B. cbn in B.
  do 5 zstep. apply evtF_done. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fprintf_i_post : forall RNG x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (j32 : list byte) (va : list cell) (rav s0v s1v s2v : word),
  mem_inv asegs m ->
  rw_cells asegs m (bv_unsigned sp) ([CB 32 j32; C8 s2v; C8 s1v; C8 s0v; C8 rav] ++ va) -> cells_size va = 48%nat ->
  rng RNG (bv_unsigned sp) 112 ->
  evtF asegs RNG (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 112)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc rav) fc None m (seg_rom asegs))
    (MS (mkR x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44f8c) fc None m (seg_rom asegs)).
Proof.
  intros until s2v. intros MI FR SZ RR. pose proof (rw_cells_bound _ _ _ _ FR) as B.
  rewrite cells_size_app, SZ in B. cbn in B.
  apply (proj1 (rw_cells_app _ _ _ _ _)) in FR. destruct FR as [FR FRV].
  do 6 zstep. apply evtF_done. reflexivity.
Qed.

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
    ms' = MS (mkR (Z_to_bv 64 0x44f8c) (Z_to_bv 64 (bv_unsigned sp - 112)) gp tp t0 t1 t2
                  a1 a0 a0 a1 (Z_to_bv 64 (bv_unsigned sp - 48)) x13 x14 x15 x16 x17
                  (Z_to_bv 64 (bv_unsigned sp - 48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x8e9a4) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2432, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp - 112)
    /\ rw_cells asegs m' (bv_unsigned sp - 112)
         [CB 32 j32; C8 s2; C8 s1; C8 s0; C8 ra; C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7]
    /\ rt_inited m'.

Section FPRINTF.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (A n : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
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
       munch [(bv_unsigned sp + -2432, bv_unsigned sp)]%Z m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
       stk asegs m1 lo (bv_unsigned sp + -112) ->
       rw_cells asegs m1 (bv_unsigned sp + -112)
         [CB 8 j8; C8 (Z_to_bv 64 (bv_unsigned sp + -48)); C8 (Z_to_bv 64 (bv_unsigned sp + -48)); C8 (Z_to_bv 64 (bv_unsigned sp + -48));
          C8 s2; C8 s1; C8 s0; C8 ra; C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] ->
       rt_got m1 -> rt_shbase m1 -> rt_inited m1 -> rt_real_printf m1 ->
       evtF asegs RNG Q (MS (mkR (Z_to_bv 64 0x44f4c) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 a1 a0
                              (Z_to_bv 64 0x1e9df) a1 (Z_to_bv 64 (bv_unsigned sp + -48)) x13 x14 x15 x16 x17
                              (Z_to_bv 64 (bv_unsigned sp + -48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x44038) fc None m1 (seg_rom asegs))) ->
    evtF asegs RNG Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x44ecc) fc None m (seg_rom asegs)).
  Proof.
    intros Q K.
    pose proof (munch_refl [(bv_unsigned sp + -2432, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold KHIGH in KLO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    Local Ltac2 Set LiaHints.tbl := fun () => "02c0?10862393880.82 11110357784.81 11475098008.80 11513985511.77 11696657560.80 11799361125.11311799361125.79 11799361125.80 11799361125.81 11799361125.82 11799361125.96 11799489569.10811801586693.93 1258288792.81  13114317212.10813114317212.11013270676710.76 14023418560.80 14277797016.11314773250736.76 15032830052.78 15104381976.96 15452344984.81 15647139096.81 16130025240.82 17288173208.11318887455772.79 19042827563.95 19343327384.81 19471543192.81 1968392128.79  20040839232.79 20517883544.11320670726424.82 20824881200.78 2115072284.76  21187167000.81 21518274460.78 21600875239.77 2185261208.80  22282192675.10822284289799.93 23400781414.75 24188925208.82 24671367001.10824673464189.93 25122868580.78 26043030976.80 26817889712.79 27147338155.11227373230610.71 27373230610.86 2770259888.79  28072922155.81 29554946712.81 29852097692.77 3020683420.77  30454027800.81 30921491992.79 31161366443.80 32068840256.79 32533658520.81 32869782320.78 33073781912.81 33865953688.80 34578542232.11334940690200.82 35633624860.79 35895327997.93 35897425113.10836345590361.10836347687549.93 36986663037.93 36988760153.10837321754422.75 37321754422.90 38088095936.77 38264599196.78 38362731800.82 38467250200.81 38889038000.79 38956189976.79 39078521240.80 39463145906.10442846560664.81 42920349976.81 43055122012.68 43121191467.81 43492410392.82 44123833920.79 44137235864.80 44484923210.93 44487020398.10844873666096.77 44899205912.81 45484308248.96 45685315612.78 45685315612.93 46235924760.81 46426210712.81 46999964426.60 47287692011.10147382493616.78 47700500248.82 48089218200.81 48325856741.10948325856743.10748893238296.82 49382291352.80 49409381016.81 49608071769.10849610168957.93 49632921830.76 49957961496.82 50125791591.77 50125791591.92 50141254592.80 50221560344.79 50543022872.82 50664164139.78 5072571819.80  50925296560.78 51234361003.80 51249199640.79 51384633319.77 51843947621.10951843947623.92 51896122520.81 52108408216.80 52151318827.81 52355859864.11352371274268.78 52431779096.82 52462798872.96 53150882660.78 53400667952.11053428579224.81 53951985688.96 53985753494.89 54002075495.77 54096612892.79 54439433112.80 54906475886.1085496416704.79  55002379676.78 55238157483.79 55890146712.80 56143470912.78 56172315833.71 56172315833.86 57052305983.71 57052305983.86 57937621272.81 57969709848.81 591692824.82   59308628304.1  59308628433.1  59308628566.1  59452298416.93 6014957611.80  60330452198.70 60335527832.81 61801762840.82 61988908056.82 62160867008.94 62431484700.11062431484700.93 62925078168.81 65212743211.80 65436951088.77 66980406808.79 68196899904.11168695373278.1086898299397.71  6898299397.86  7987385664.78  8603416747.79  8788598064.78  9096189976.96  00000800@00H00I00Q00R00S00T00U00V00W00\00a00i00j00k00l01001801901:01B01J01R01Z01b01c01h02002802<02@02H02P02Q02R02Z02[02\02d02e02f02g02o03;03G03H03L03M03R03S03T03U03Z03b03c03d03l04404904=04E04F04N04V04^04f04g05305?05K05W05c05o06=06K06O06P06X06`06a06i07107207:07B07F07K07S07W07_07`07a07b07j08208308408<08D08H08I08J08R08Z08[08\08d08l09409@09L09M09U09V09W09[09c09k0:00:50:60:;0:C0:D0:E0:F0:N0:V0:[0:c0:d0:l0;40;50;60;>0;F0;G0;H0;I0;Q0;R0;V0;W0;\0;d0;h0;i0;j0;n0<20<:0<B0<J0<N0<R0<V0<W0<\0<]0<e0<m0=50=90=:0=;0=C0=H0=I0=Q0=U0=V0=W0=X0=\0=a0=b0=jS2LO3KLOS2LO3KLOS2LO3KLOSS2LO3KLOSSSSSSS3HspS3HspS2LO3KLOSSSS2HBS2LO3KLOSSS2LO3KLOS2LO3KLOS2LO3KLOS2LO3KLOS2LO3KLOSS3SPRS2LO3KLOS2LO3KLOS2HBS2HBS2LO3KLOS2LO3KLOSSS2LO3KLOSSS2LO3KLOFFSS2LO3KLOS2LO3KLO3HspS2LO3KLO3HspSS2HBSS3SPRFFSS3SPRS2LO3KLOSSS2LO3KLOS2LO3KLOS3SPRS2HBS2LO3KLOSS2LO3KLOS2LO3KLOS2LO3KLOS2LO3KLOSS2LO3KLO3HspS2LO3KLO3HspS2LO3KLO3HspS2LO3KLO3HspS2LO3KLO3HspS2LO3KLO3HspS2LO3KLO3SPR1HS2LO3KLO3SPR1HS2HBSS2LO3KLOS2LO3KLOSS2LO3KLOS2LO3KLOSS2LO3KLOS2LO3KLOS2LOS3SPRS2LO3KLOS2HBS2LO3KLOFFSS2LO3KLOS2LO3KLOSSS2LO3KLOS2LO3KLOS2LOSSS2LO3KLOS2LO3KLOSSS2LO3KLOS2LO3KLOS2LO3KLOS2LO3KLO3HspS2LO3KLO3HspSS2LO3KLOSSS2HBS2LO3KLOS2LO3KLOS3SPRS3SPRSS3SPRS2LO3KLOSSSS2LO3KLOS2LO3KLOS3SPRS2LO3KLOSS2LO3KLOS2LO3KLOSSS2LO3KLOS2LO3KLOSSSS2LO3KLOSS2HBSS3SPRS2LO3KLOS2HBSSS2LOS2LOS2LO3KLOS2LO3KLOS2LO3KLOS2K1S2K2S2K3SS3SPRSS2LO3KLOS2LO3KLOS2LO3KLOS2HBSSS2LO3KLOS3SPRSS2LO3KLOS2HBSFFS2HBS3SPRSS2LO3KLO".
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
    evtF asegs RNG MID (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x44ecc) fc None m (seg_rom asegs)).
  Proof.
    apply fprintf_i_A. intros m1 j8 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 MU1 WM1 MI1 ST1 FR1 GOT1 SHB1 INI1 RPF1.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold KHIGH in KLO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    Local Ltac2 Set LiaHints.tbl := fun () => "00F0?11799456952.81 11801586693.10513885248473.11014262234230.10617222273888.98 18442817054.82 24673464189.10527375328819.82 31382798176.98 35895327997.10536986663037.10537321754422.86 44484923210.10546999964426.80 4917892871.105 49610168957.10551843947620.10554030295446.10156170217624.82 60318033760.98 62431484700.1066896203300.82  00000;00@00A00B00C00G00S00T00U00a00m01;01<01@01A01M01N01O01P01Q01R01SS2LO3KLO2NAS3HspSSSS2LOS2LO3KLO3HspFSS2LO3KLO3HspS2LO3KLO3HspS2LO3KLO3SPR1HFS2LOFS2LO3KLO3HspSSSSSF".
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
      lazymatch goal with FR : rw_cells asegs mf (bv_unsigned sp + -112) (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) |- _ =>
        pose proof (rw_cells_merge asegs mf _ [] [c1; c2; c3; c4] rest FR) as FRm; cbn [app cells_size csize Nat.add] in FRm end end.
    do 14 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption. exact FRm.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  Variables (sstr : list byte) (RLO RHI : Z).
  Notation Sa := (bv_unsigned a2).
  Notation NS := (Z.of_nat (length sstr) + 1)%Z.
  Hypothesis LAY : rt_layout m.
  Hypothesis SSTR : bytes_at asegs m Sa (sstr ++ [Z_to_bv 8 0]).
  Hypothesis SNOZ : Forall (fun b : byte => bv_unsigned b <> 0%Z) sstr.
  Hypothesis SEPS : (Sa + NS <= bv_unsigned sp - 2432 \/ bv_unsigned sp <= Sa)%Z.
  Hypothesis APPS : app_blk Sa (Sa + NS).
  Hypothesis SPOS : (0 < Sa)%Z.
  Hypothesis USTR : unpoisoned m Sa (Sa + NS).
  Hypothesis NSZ : (NS <= 2^40)%Z.
  Hypothesis R1 : (RLO <= Sa /\ Sa + NS <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z.
  Hypothesis WR1 : wr_at asegs m (shad RLO) (shad RHI - shad RLO).
  Hypothesis RS : rng RNG Sa NS.
  Hypothesis RSH1 : rng RNG (shad RLO) (shad RHI - shad RLO).
  Hypothesis PCS : printf_common_s_stmt A n.

  #[using="A n MI ST LO KLO GOT SHB INI CKP RPF A1 NA FZ RI RSTK RSHF sstr RLO RHI LAY SSTR SNOZ SEPS APPS SPOS USTR NSZ R1 WR1 RS RSH1 PCS"] Lemma fprintf_i_pre_s :
    evtF asegs RNG MID (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x44ecc) fc None m (seg_rom asegs)).
  Proof.
    apply fprintf_i_A. intros m1 j8 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 MU1 WM1 MI1 ST1 FR1 GOT1 SHB1 INI1 RPF1.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold KHIGH in KLO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    Local Ltac2 Set LiaHints.tbl := fun () => "00V0?11799440546.10211801389858.10111801586693.12911803405368.99 13885248473.13214262234230.12814788810421.10614790997494.10917219881159.12018448874142.10621594911267.10924673464189.12927369286323.10627923144266.10631380405447.12035895327997.12936986663037.12937321754422.11038270114779.10538285077374.12144484923210.12946999964426.96 4917892871.129 49610168957.12951843947620.12754030295446.12556185189400.10659503987035.10659504015996.12260328355015.12060866711165.10662431484700.1286515440607.106 6611983004.109 68185727392.1066911148708.106 9403517786.100 9405451517.129 00000A00G00[00o01001101@01O01P01T01U01a01b01c01d02002<02M02N02O02P02T02U02a02b02c02d02e02f02g02m02n02o03003503603A03MS2LO3KLO4SEPS3AS'S4SEPSS2LO3KLO4SEPS2R13HspS2LO3KLO2NA4SEPS3AS'SSS2LO3KLO2R13SPRS2LO3KLO2R13SPRSS2LOSS2LO3KLO3HspFFSS2LO3KLO3HspS2LO3KLO3HspS2LO3KLO2R13SPR1HSSFS2LOFS2LO3KLO3HspSSSSSSS4SEPSSFFS3SPRFS2LO3KLO2R1S2LO3KLO3Hsp".
assert (RSTK' : rng RNG (bv_unsigned sp + -2432) 2432) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof APPS as APPS'. destruct APPS' as [LES AS']. unfold KLOW, KHIGH, KEND in AS'.
    assert (FZ1 : shadow_bytes m1 (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0%Z)).
    { eapply shadow_bytes_munch; [exact FZ | exact MU1 |]. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
    assert (LAY1 : rt_layout m1).
    { eapply rw_cells_transport; [exact LAY | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    assert (SSTR1 : bytes_at asegs m1 Sa (sstr ++ [Z_to_bv 8 0])).
    { eapply bytes_at_transport; [exact SSTR | exact MU1 |]. rewrite length_app. cbn [length disjoint_from]. lia. }
    assert (USTR1 : unpoisoned m1 Sa (Sa + NS)).
    { eapply unpoisoned_munch; [exact USTR | exact MU1 |]. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
    assert (WR11 : wr_at asegs m1 (shad RLO) (shad RHI - shad RLO)) by (eapply wr_at_transport; eassumption).
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
      lazymatch goal with FR : rw_cells asegs mf (bv_unsigned sp + -112) (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) |- _ =>
        pose proof (rw_cells_merge asegs mf _ [] [c1; c2; c3; c4] rest FR) as FRm; cbn [app cells_size csize Nat.add] in FRm end end.
    do 14 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption. exact FRm.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End FPRINTF.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition vprintf_i_mid (ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 x13 x14 x15 x16 x17 t3 t4 t5 t6 m' j24 j16,
    ms' = MS (mkR (Z_to_bv 64 0x44b70) (Z_to_bv 64 (bv_unsigned sp - 96)) gp tp t0 t1 t2
                  a0 (Z_to_bv 64 0x9d500) (Z_to_bv 64 0x9d500) a0 a1 x13 x14 x15 x16 x17
                  a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x8e9a4) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2416, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp - 96)
    /\ rw_cells asegs m' (bv_unsigned sp - 48) [CB 24 j24; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' (bv_unsigned sp - 96) [CB 16 j16; C8 s2; C8 a1; C8 a0; C8 (Z_to_bv 64 0x44000)]
    /\ rt_inited m'.

Section VPRINTF.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (A n : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
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
    evtF asegs RNG (vprintf_i_mid ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x43f9c) fc None m (seg_rom asegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -2416, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold KHIGH in KLO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    Local Ltac2 Set LiaHints.tbl := fun () => "03H0?10862393880.11310862393880.79 11093997488.11011696657560.11411696657560.81 11723034140.76 11799361125.11311799361125.11411799361125.11611799361125.13111799361125.79 11799361125.81 11799361125.82 11799361125.98 11799489569.10911799489569.14211799489570.12511801586693.92 11803324321.11811805421443.85 12037418212.77 13177566513.12113284814180.92 13284814186.94 13885248473.14614262234230.14214277797016.11414277797016.82 14793086774.74 14793086774.90 15104381976.11615104381976.82 15647139096.11415647139096.98 16130025240.11316130025240.79 16475027684.11017288173208.11417288173208.82 18097663185.11119042827563.11519042827563.81 19340579248.95 19664730524.11120517883544.11420517883544.82 22282192672.12522284289799.92 22387597248.77 23077509607.13023139947184.11324671367001.10924671367001.14224671367002.12524673464189.92 25042987031.13125393266480.79 25613863711.11925779550180.11026743380460.13126939498908.11126939498908.79 26939498908.95 27147338155.11327147338155.81 28072922155.11228072922155.78 28232796652.13128406852928.79 29158023216.11129323744831.70 29738897271.12629738897271.12831377886384.79 31378308326.69 31384895300.13431704748700.11132907263168.11234440526528.80 34578542232.11434578542232.82 34940690200.11334940690200.79 35001395692.13135142651312.11135895327997.92 35897425113.10935897425113.14235897425114.12536178739012.13436345590361.10936345590361.14236345590362.12536347687549.92 36986663037.92 36988760153.10936988760153.14236988760154.12537062796780.13137438167600.78 37736273202.13837821204774.10138467250200.11438467250200.98 38908001203.11439377301110.1113946739303.109 40460011584.80 41194412848.11141873551410.11941873551411.86 41873552432.10341875649554.70 41897576499.11442250564406.10742250564406.12342920349976.11442920349976.98 43055122012.67 43407189580.12943422820272.76 43678327964.78 44137235864.11444137235864.81 44484923210.92 44487020397.12544487020398.10944487020398.14244960421824.11445484308248.11645484308248.82 45507666326.88 46235924760.11446235924760.98 46462227904.96 46998232647.10347287692008.11847289789135.85 47349350067.11647561401098.59 47700500248.11347700500248.79 47804764645.78 47804764650.11047804764650.94 4915795747.109 4915795747.142 49382291352.11449382291352.81 49608071769.10949608071769.14249608071770.12549610168957.92 49957961496.11349957961496.79 50148821093.78 50644243556.11050644243556.14150644243562.12750977580352.11252108408216.11452108408216.81 52277671964.11152277671964.12852277671964.14252355859864.11452355859864.82 52462798872.11652462798872.82 53710135069.10353951985688.11653951985688.82 54628007404.13154906475887.12654906475887.93 55812340146.10555890146712.11455890146712.81 55952418663.75 56003195754.11256170217624.86 56170217625.11956170218651.10356172315833.70 56980320960.11157405284894.86 57937621272.11457937621272.98 58383961523.11359308628304.1  59308628433.1  59308628566.1  59308628695.1  59510497308.93 59510497308.95 60681498140.11062065839047.12862999281728.11264043097572.12564043097578.12764284135708.11365212743211.11365212743211.97 67210899763.11468695373279.12668695373279.93 6896202279.103 6896203300.86  6896203301.119 6898299397.70  7495246620.79  7589930820.134 8603416747.113 8603416747.80  9096189976.116 9096189976.82  00000800@00A00I00Q00R00S00T00U00V00W00X00Y00Z00_00d00i00n01901D01E01F01G01H01I01J01R01Z01h02602>02F02N02V02^02f02g02o03703803=03B03C03D03L03T03U03V03Z03_03`03l04804D04P04Q04R04V04W04_04`04a04b04g04l05105605>05B05C05G05H05I05J05K05L05M05Q05U05]05e05m06506=06>06J06V06b06n06o07;07G07S07_07k08708C08O08W08X08Y08]08e08m08n08o09009409509609709809909:09H09V09^09f09j09n09o0:00:80:@0:A0:B0:C0:D0:H0:P0:X0:Y0:a0:i0:m0:n0:o0;00;10;50;=0;E0;F0;G0;H0;I0;J0;R0;Z0;f0<20<>0<J0<R0<Z0<[0<\0<]0<^0<b0<j0=20=30=40=50==0=E0=M0=U0=Y0=a0=i0>10>20>30>40><0>D0>E0>F0>G0>H0>I0>J0>N0>R0>Z0>b0>c0>g0>k0>o0?30?40?50?60?70?;0?<0?=0?>0?C0?H0?I0?J0?K0?L0?M0?N0?O0?P0?Q0?V0?[0?c0?kS2LO3KLOS2LO3KLOSS2LO3KLOS2LO3KLOSSSSSSSSSS3HspS3HspS3HspS3HspS2LO3KLO2NAS2LO3KLO2NASSSSSSS2LO3KLOS2LO3KLOS2LO3KLO3SPR1HS2LO3KLO3SPR1HS2LO3KLOS2LO3KLOS2LO3KLOS2LO3KLOS2LO3KLOS2LO3KLOSS2LO3KLOS2LO3KLOSS3SPRS3SPRSSS2LO3KLOS2LO3KLOFFS2HBS3SPRSS2LO3KLO3HspS2LO3KLO3HspS2LO3KLO3HspS2LO3KLO3HspSSS2LOSS2LO3KLOSSSS3SPRS3SPRS3SPRS3SPRS2LO3KLOS2HBSS2LOSSSSSSS2HBS2HBS2LO3KLOS2LO3KLOS2LO3KLOS2LO3KLOS2LO3KLOSS2LO3KLO3HspS2LO3KLO3HspS2LO3KLO3HspS2LO3KLO3HspSS2LO3KLO3HspS2LO3KLO3HspS2LO3KLO3HspS2LO3KLO3HspS2LO3KLO3HspS2LO3KLO3HspS2LO3KLO3HspS2LO3KLO3HspS2LO3KLOSSS2LOS2LO3KLOS2LO3KLOSSSS2HBSFFFFSS2LO3KLO3SPR1HS2LO3KLO3SPR1HS2LO3KLOS2LO3KLOS2LOS2HBSSS2LO3KLOS2LO3KLOFFFFS2HBS2LO3KLOS2LO3KLOSS2LO3KLOS2LO3KLOS2HBSSSSS2LOS2LO3KLOS2LO3KLOSSSFFS2LO3KLOS2LO3KLOS2LO3KLO3HspS2LO3KLO3HspS2LO3KLO3HspS2LO3KLO3HspS2LO3KLOS2LO3KLOSSSSS2HBS2LO3KLOS2LO3KLOSSSS2LO3KLOS2LO3KLOS2LO3KLOS2LO3KLOS2LOS2LO3KLOS2LO3KLOS2LO3KLOSSSS2LO3KLOS2LO3KLOSSSSSSS2HBS2LOS2LO3KLOS2LO3KLOSS2K1S2K2S2K3S2K4SSSSS2HBSSSS3SPRS3SPRSSSFFFFSSS3SPRS3SPRS2LO3KLOS2LO3KLO".
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
    match goal with H : stk asegs _ lo (bv_unsigned sp + -48) |- _ => carve_frame 48%nat H end.
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
      lazymatch goal with FRa : rw_cells asegs mf (bv_unsigned sp + -48) (?c1 :: ?c2 :: ?c3 :: ?rest) |- _ =>
        pose proof (rw_cells_merge asegs mf _ [] [c1; c2; c3] rest FRa) as FRm1; cbn [app cells_size csize Nat.add] in FRm1 end;
      lazymatch goal with FRb : rw_cells asegs mf (bv_unsigned sp + -96) (?c1 :: ?c2 :: ?rest) |- _ =>
        pose proof (rw_cells_merge asegs mf _ [] [c1; c2] rest FRb) as FRm2; cbn [app cells_size csize Nat.add] in FRm2 end end.
    do 15 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption. exact FRm1. exact FRm2.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End VPRINTF.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Corollary vprintf_i_pre_d : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2416)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> rt_inited m -> rt_ckpf m -> rt_real_printf m ->
  a0 = Z_to_bv 64 FMT_D ->
  shadow_bytes m (shad (FMT_D - 64)) (shad (FMT_D + 3 + 64)) (fun _ => 0%Z) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad (FMT_D - 64)) (shad (FMT_D + 3 + 64) - shad (FMT_D - 64)) ->
  evtF asegs RNG (vprintf_i_mid ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x43f9c) fc None m (seg_rom asegs)).
Proof. intros. eapply vprintf_i_pre; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast. { unfold FMT_D. Local Ltac2 Set LiaHints.tbl := fun () => "0010=2309797376.51000001S".
lia. } exact printf_common_d_stmt. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Corollary fprintf_i_pre_toobig : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2432)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> rt_inited m -> rt_ckpf m -> rt_real_printf m ->
  a1 = Z_to_bv 64 FMT_TOOBIG ->
  shadow_bytes m (shad (FMT_TOOBIG - 64)) (shad (FMT_TOOBIG + 32 + 64)) (fun _ => 0%Z) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad (FMT_TOOBIG - 64)) (shad (FMT_TOOBIG + 32 + 64) - shad (FMT_TOOBIG - 64)) ->
  evtF asegs RNG (fprintf_i_mid ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44ecc) fc None m (seg_rom asegs)).
Proof. intros. eapply fprintf_i_pre_int; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast. { unfold FMT_TOOBIG. Local Ltac2 Set LiaHints.tbl := fun () => "0010>68284883888.51000001S".
lia. } exact printf_common_toobig_stmt. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Definition fprintf_i_pre_s_stmt (A n : Z) : Prop :=
  forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (sstr : list byte) (RLO RHI : Z),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2432)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> rt_inited m -> rt_ckpf m -> rt_real_printf m -> rt_layout m ->
  a1 = Z_to_bv 64 A ->
  shadow_bytes m (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0%Z) ->
  bytes_at asegs m (bv_unsigned a2) (sstr ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0%Z) sstr ->
  (bv_unsigned a2 + (Z.of_nat (length sstr) + 1) <= bv_unsigned sp - 2432 \/ bv_unsigned sp <= bv_unsigned a2)%Z ->
  app_blk (bv_unsigned a2) (bv_unsigned a2 + (Z.of_nat (length sstr) + 1)) -> (0 < bv_unsigned a2)%Z ->
  unpoisoned m (bv_unsigned a2) (bv_unsigned a2 + (Z.of_nat (length sstr) + 1)) -> (Z.of_nat (length sstr) + 1 <= 2^40)%Z ->
  (RLO <= bv_unsigned a2 /\ bv_unsigned a2 + (Z.of_nat (length sstr) + 1) <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z ->
  wr_at asegs m (shad RLO) (shad RHI - shad RLO) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad (A - 64)) (shad (A + n + 64) - shad (A - 64)) ->
  rng RNG (bv_unsigned a2) (Z.of_nat (length sstr) + 1) -> rng RNG (shad RLO) (shad RHI - shad RLO) ->
  evtF asegs RNG (fprintf_i_mid ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44ecc) fc None m (seg_rom asegs)).

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
