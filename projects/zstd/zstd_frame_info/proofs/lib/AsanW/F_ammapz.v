(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import MM_syscalls.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import SysStepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg AProto ABase AKit AKit2 RT_stubs F_ammap.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition mmapz_entry := 0x651d4.
End CANSEC1.
Notation MMAPZ_STACK := 320 (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Definition mmapz_post (RNG : footprint) (sp : word) (a size lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG' /\ fp_bw RNG'
  /\ a mod 4096 = 0 /\ 0 < a /\ a + size <= ATOP
  /\ munch [(bv_unsigned sp - MMAPZ_STACK, bv_unsigned sp); (a, a + size)]%Z m m' /\ wmono asegs m m'
  /\ mem_inv asegs m'
  /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' a [CB (Z.to_nat size) (repeat (Z_to_bv 8 0) (Z.to_nat size))]
  /\ rng RNG' a size /\ rng RNG' (shad a) (shlen size)
  /\ rmap_cells m'.

#[using="Type"] Lemma mmapz_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    (FRESH : Z -> bool)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (size lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - MMAPZ_STACK ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 size -> size mod 4096 = 0 -> 0 < size -> size < 2^40 -> bv_unsigned a1 <> 0 ->
  rmap_cells m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  (forall a, FRESH a = true -> 0 < a -> a + size <= ATOP -> AIMG_HI <= a /\ (a + size <= bv_unsigned sp - 48 \/ bv_unsigned sp <= a)) ->
  (* [comment removed for export] *)
  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + size <= ATOP -> fp_le RNG RNG' ->
      implS asegs RNG' (K a) (epostF Q) ms') ->
  (* [comment removed for export] *)
  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> mmapz_post RNG sp a size lo m RNG' m' ->
      implS asegs RNG' (K a) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 a) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap 0 size 3 34) (adec_mmap ATOP size 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 mmapz_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> SAL SPOS SZ NAME RC RIMG RSTK FROK UNR KONT.
  pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & GOT & DPM & MLIM). word_range a1 A1R.
  unfold AIMG_HI, mmapz_entry in *. word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - MMAPZ_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  eapply (implF_ebind _ _ _ _ _ _ _
            (fun a RNG' ms' => (FRESH a = false /\ 0 < a /\ a mod 4096 = 0 /\ a + size <= ATOP /\ fp_le RNG RNG')
                            \/ FRESH a = true /\ exists m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
               mmapz_post RNG sp a size lo m RNG' m' /\
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 a) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom asegs))).
  2: { intros a RNG' ms' [(NF & P1 & P2 & P3 & P4)|[FR PO]]; [apply UNR; assumption|].
       destruct PO as (m' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & PO & ->).
       eapply KONT; [exact FR | exact PO]. }
  (* [comment removed for export] *)
  iprefix.
  Local Ltac2 Set LiaHints.tbl := fun () => "03@0?10667180602.78 10965657262.74 11613226300.77 1162083360.80  1162083374.77  11647286254.72 11805467289.72 11805467289.74 11805467289.75 11805467289.76 11805467289.77 11805467289.78 12119712956.76 12429510126.10213425838126.74 13659793162.87 14761575534.74 14866570234.74 15788225262.78 16540621984.79 16540621996.73 17776320428.73 17778417576.10117976286208.2  1800609155.102 1800609155.74  1809810926.78  18225867374.72 18230891272.89 18689773242.75 18893895214.74 19879235054.78 21811810457.78 2190890265.76  21934774638.78 22219720579.76 22219720579.79 22232942.76    22249017454.75 22389541692.72 22885694752.70 22927418606.77 2350913305.76  23619845358.76 23715658734.78 24018494190.77 2435347822.76  24468186791.76 24487705898.71 24559885228.75 24559885230.78 24638473347.10224974828534.10225071629079.10225240764910.72 25627738222.10225878270253.74 25878270255.77 26015742015.89 26429361813.4  2649471752.89  27066288442.75 27408782881.79 27408782895.76 27778003822.74 27797263342.75 27907155234.89 28417259964.74 29349361518.77 29448452775.76 29514832494.74 2993314286.72  30231011258.76 30603927662.74 31378308326.66 31929422314.77 31940628442.68 32300784295.78 32377744366.10232501562499.78 32501562499.81 32631783278.76 33680001082.75 33890036512.80 33890036526.77 33962954137.75 34122977177.78 34140524150.79 34430152252.75 35082589626.76 35100153219.75 35100153219.76 35900719086.78 36107562391.92 36576291080.89 36654913774.75 37609348206.75 37827660420.67 37845668334.10238214450030.76 38534813827.75 38534813827.78 38725888878.75 39058966403.76 39058966403.79 39238442350.76 40091925677.74 40091925677.75 40333419028.88 40457739452.74 40608002030.72 42115887662.74 42488118638.74 42882700782.75 4288869222.89  43045295752.89 43059266230.64 43175993206.10143985854248.10143987951407.74 43988483203.10143988483203.72 44223460412.78 44464229507.78 44464229507.81 4497338734.76  45221239098.10245415010670.74 45848756903.72 46356275438.75 46382356647.75 46468661564.10247230136046.77 4751458172.69  49562070382.76 49649769127.75 49710714478.75 49725372071.75 49750950894.10250244754108.76 50703419246.76 51254863854.75 51509148455.74 51585900270.76 51678667180.75 51678667182.78 51711223320.88 52105090727.74 52220997238.10253540834542.77 53767577772.73 53769674920.10154243526019.10254243526019.74 54367113454.78 56064834414.74 56084093934.75 56241442027.10156255680316.78 563227834.74   56759370246.7  56763417884.86 56765693756.89 56765693885.88 56771238972.10256771238972.10357745675194.74 58776000537.75 58843038472.89 59308628179.4  59314873579.7  60537240323.74 60537240323.80 60858483367.1026094239292.75  61170136174.75 61439603310.74 6165337146.77  61988516505.77 62283267516.75 63002572398.78 63235321891.10063235321901.71 63305555623.74 63341493050.78 64997134979.10264997134979.75 65104334021.87 65106320572.3  65666169454.75 65704139943.77 65896949806.74 66021542019.77 66021542019.80 66554270958.78 67134106962.10267643606599.69 6783195886.78  68062769646.74 68501319406.75 68589449454.74 7373603310.75  7735119015.78  8405736896.102 8405736896.103 8583720762.72  9107720828.74  9956545262.75  00000500>00B00F00J00S00T00U00V00W00X00Y00]00f00o01001901>01G01K01O01S01W01]01^01_01h02102602;02D02M02N02O02X02Y02Z02c02l03003403=03>03G03P03Y03b03c03d03h03l03m03n03o04804A04E04I04V04[04`04e04i04m05605?05C05G05P05Q05Z05c05h06106206;06D06E06N06O06P06Y06^06b06f06g06h06i06m07207307407=07D07I07R07[07_07h08108208308<08=08>08G08K08O08T08X08a08j09309<09=09B09F09G09K09O09P09Q09U09V09W09`09e09n09o0:80:90:=0:F0:G0:P0:Q0:Z0:[0:d0:h0;10;:0;;0;D0;H0;L0;M0;N0;O0;X0;\0;`0;a0;b0;k0<40<=0<A0<E0<J0<Z0<h0=00=>0=F0=N0=S0=T0=Y0=f0>;0><0>=0>>0>B0>K0>T0>Y0>Z0>^0>g0>k0>o0?00?50?60?70?@0?I0?R0?S0?\0?]0?^0?g0@90@:0@C0@L0@U0@^0@g0@h0@i0@j0@o0A30A<S3SPRS4CEIL2LOS2HBS2LOS2LOS4CEIL2LOSSSSSSS2HBS4CEIL2LOS4CEIL2LOSS4CEIL2LOS3SPRS4CEIL2LOS2LOS2LOS2LOS2LOS4SPOSSSS4CEIL2LOS4CEIL2LOS3AIMS3SPRS4CEIL2LOS4CEIL2LOSSS4CEIL2LOSSS4CEIL2LOS4CEIL2LOS2HBS2LOS4CEIL2LOSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSSS2LOS2LOSSSS4CEIL2LOS4CEIL2LOS2LOS2LOS4CEIL2LO3AM3S3SALS3AIMS3SPRS2LOS2LOS4CEIL2LOS4CEIL2LOS2LOS2HBS4CEIL2LOSS4CEIL2LOS4CEIL2LOS3SPRS4CEIL2LOSS4SPOS2SZS4SPOS2SZSS4CEIL2LOSSS4CEIL2LOS3SPRS2LOS2LOSSSS2HBS3SPRSSS4CEIL2LOS3AIM1HS3AIMS4CEIL2LOS4CEIL2LOS2LOS4CEIL2LOS4CEIL2LOSSS4CEIL2LOSSS4CEIL2LOS2LOS2LOS3AM3S2HBS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSS3AIMS2LOSS2LOS2LOSSS2HBSSS4CEIL2LOS3SPRS4CEIL2LOSS4CEIL2LOSS2HBS4CEIL2LOSS4CEIL2LOSS4CEIL2LOSS4CEIL2LOS2HBS4CEIL2LOS4CEIL2LOSS4CEIL2LOS2LOS2LOSSSS4CEIL2LOS2LOS2LOSSS4CEIL2LOS4CEIL2LOS4CEIL2LOS2LOS2HBS3SPRS4SPOS3AM23AM31HS4SPOS3AM23AM3S3AM22K1S4SPOS3AM23AM3S3AM22K1S3AM22K1S3SPRSS3AIMS4NAME3A1R2K0S4SPOS3AM32K11H2LT2K2SSSS2HBS4CEIL2LOS4CEIL2LOS3SPRSS2HBS4CEIL2LOS2LOS2LOSS3SPRSSS4SPOS2SZS4SPOS2SZS4CEIL2LOSS4CEIL2LOSSS4CEIL2LOS4CEIL2LO4SPOS3AM3SS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSFFS3SPRS2HBS4CEIL2LO".
carve_frame 48%nat ST.
  step. step. step. step. step.                                (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                                  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
  setreg 9 (Z_to_bv 64 size) ltac:(rewrite land_align4096 by lia; f_equal; clear -SAL SPOS SZ; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  step. step. step. step. step.                                (* [comment removed for export] *)
  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  carve_frame 272%nat ST.
  step. step. step. step. step. step. step. step.              (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 NAME A1R. lia. }   (* [comment removed for export] *)
  step. step. step. lstep.                                     (* [comment removed for export] *)
  zstep. step. if_lit.                                         (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  step. step. step. step. step. step. step. step. step.        (* [comment removed for export] *)
  release_frame FR0 ST (bv_unsigned sp + -48).
  step. setreg 13 (Z_to_bv 64 34) ltac:(vm_compute; reflexivity).   (* [comment removed for export] *)
  step. step. step. step. step.                                (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  icallk rt_mmap_stubP.
  intros a RNG' ms' (rsp & HF & Hdec & ->).
  destruct (adec_mmap_rw_Some _ _ _ Hdec) as (ci & -> & AM1 & AM2 & AM3).
  pose proof (page_round_up_mult size SAL ltac:(clear -SPOS; lia)) as PRU. unfold mmap_len in *. rewrite PRU in AM3. rewrite PRU.
  pose proof (fstepS_mmap_grant 0 size 34 _ RNG RNG' HF (eq_refl : Z.land 34 MAP_NORESERVE = 0)) as GR. cbn [eff_ret] in GR.
  rewrite (unsigned_lit a) in GR by (clear -AM2 AM3 SPOS; lia). rewrite (unsigned_lit size) in GR by (clear -SPOS SZ; lia).
  rewrite PRU in GR. specialize (GR ltac:(unfold page_size; exact AM1)). destruct GR as [GR1 GR2].
  pose proof HF as HF0. destruct HF0 as [[FPLE _] [_ BW]].
  destruct (FRESH a) eqn:HFR.
  2: { fstepS_transport HF. apply evtF_done. left. split; [reflexivity|]. split; [exact AM2|]. split; [exact AM1|]. split; [atop_facts; exact AM3| exact FPLE]. }
  destruct (FROK a HFR AM2 AM3) as [AIM AFR].
  fstepS_transport HF.
  unfold rt_regs. cbn [eff_ret]. rewrite eff_mem_zeros.
  replace (ret_pc (Z_to_bv 64 414300)) with (Z_to_bv 64 414300 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  apply (munch_weaken _ [(bv_unsigned sp - MMAPZ_STACK, bv_unsigned sp); (a, a + size)]%Z) in MU.
  2: { unfold sub_fp. cbn [outside]. clear. intros x Hx. tauto. }
  sys_mem_zeros.
  (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step. step. step. if_cases K1; zify_cond K1. 2: { exfalso. clear -K1 AM3 SPOS. lia. }   (* [comment removed for export] *)
  zstep. step.                                                 (* [comment removed for export] *)
  setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 a) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
  step. step. step. step. step. step.                          (* [comment removed for export] *)
  step. step. step. if_cases K2; zify_cond K2. 2: { exfalso. clear -K2 AM3 SPOS. lia. }
  zstep. step.
  setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 a) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
  step. if_lit.                                                (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  step. step. step. step. if_lit. step.                        (* [comment removed for export] *)
  step. step. step. step. step. step. step.                    (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -48) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  apply evtF_done. right. split; [reflexivity|].
  do 15 eexists. split. 2: reflexivity.
  unfold mmapz_post.
  split; [exact FPLE|]. split; [exact BW|]. split; [exact AM1|]. split; [exact AM2|]. split; [exact AM3|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [exact ZNEW|]. split; [exact GR1|]. split; [exact GR2|].
  unfold rmap_cells. repeat (split; [assumption|]). assumption.
  Unshelve. all: apply ref_ro_addr_false; right; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rmapd_entry := 0x6d9a4.
#[using="Type"] Lemma rmapd_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RMAPD_STACK ->
  mem_inv asegs m ->
  a1 = Z_to_bv 64 addr -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 0 ->
  addr mod 4096 = 0 -> size mod 4096 = 0 -> 0 < size -> AIMG_HI <= addr -> addr + size < 2^63 ->
  rmap_cells m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  (forall a RNG' ms', a <> addr -> 0 < a -> a + size <= ATOP -> implS asegs RNG' (K a) (epostF Q) ms') ->
  (forall RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      rmap_postD RMAPD_STACK RNG sp addr size lo m RNG' m' ->
      implS asegs RNG' (K addr) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap addr size 3 50) (adec_mmap ATOP size 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rmapd_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> -> -> AAL SAL SPOS A0 ASZ RC RIMG RSTK UNR KONT. unfold AIMG_HI in A0.
  pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & GOT & DPM & MLIM).
  unfold rmapd_entry in *. word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - RMAPD_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  eapply (implF_ebind _ _ _ _ _ _ _
            (fun a RNG' ms' => (a <> addr /\ 0 < a /\ a + size <= ATOP) \/ a = addr /\ exists m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
               rmap_postD RMAPD_STACK RNG sp addr size lo m RNG' m' /\
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom asegs))).
  2: { intros a RNG' ms' [(NE & P1 & P2)|[-> PO]]; [apply UNR; [exact NE | exact P1 | exact P2]|].
       destruct PO as (m' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & PO & ->).
       eapply KONT. exact PO. }
  (* [comment removed for export] *)
  iprefix.
  step. step. step. step.                                      (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  Local Ltac2 Set LiaHints.tbl := fun () => "03Y0>10667180602.7511303324790.7511805467289.6911805467289.7111805467289.7211805467289.7311805467289.7512352412732.7212974414830.711340665966.71 14689973870.7115107956284.7515600526930.7115779085422.7115788225262.7515813913888.7615813913902.7416290529959.7216622434386.7117151130279.7217544628206.721772731779.73 1772731779.75 17776320428.7017778417576.9217976286208.2 17995455655.711809810926.75 18363204284.7118689773242.7318890355993.7318900419239.7519139298862.9319376804346.9319391258279.7319625521020.9319879235054.7519970277031.7120447870595.7520447870595.772124193155.71 2124193155.91 21934774638.7522102740889.7522163107130.7222232942.73   22249017454.7222711797486.6922927418606.7523012552174.7223619845358.7323715658734.7523882872046.6924018494190.7524179267756.7224179267758.742435347822.73 24390924092.6924409718067.7124630998586.7225071629079.9326115614154.9326431752469.6 27066288442.7227408782893.7127408782895.7327514742894.7127797263342.7229349361518.7530023022247.7330196181434.7130231011258.7330403814844.713071671100.75 31319825774.7231539821806.69315996476.72  31929422315.7331940628442.6532127996803.7132127996803.9332631783278.7332651489978.7133148315118.7133941110538.7834417933740.7234417933741.7134570277878.9334924112160.6635082589626.7335111703823.7135111703823.763551070382.93 35900719086.7536107562391.8336113525291.9336115622447.7136180999398.6336590710439.7336981022702.7237609348206.7338214450030.7338399784046.7239219183342.7239238442350.7339571573379.7539571573379.7740613224310.9242085054489.7342236688921.7342309226734.7242501437472.9342501437472.9442503534630.7042505299482.6542509314849.7742511604512.8042511604641.7942775782659.9342817538363.8042831019478.7142882700782.7243059266230.614339538087.72 43413664432.7143985854248.9243987951407.714413803118.71 44187290284.804472014211.72 4472014211.73 4497338734.73 45352467587.7545352467587.7746232973498.7146234544622.7246895624871.7547230136046.7547296502915.7247296502915.7448538816594.7148673721966.7149255081006.9349288693539.8049562070382.7349710714478.7349903997356.8050645511577.7550703419246.7351041686382.7151124399687.665114850435.72 5114850435.93 5120733337.72 51254863854.7351495837550.6951585900270.7351612993474.6 5289276057.75 53540834542.7553676604142.6953767577772.7053769674920.9253853382510.7153904676268.8054300395630.7154367113454.755496517358.71 5575378976.76 5575378990.74 55770193284.6456084093934.7256426686290.7156712086766.7256759370246.7 56779838332.6558618836718.7258762852128.7658762852142.7459192637571.6959192637571.9259314873579.7 59314873579.8 59758911548.7560274535852.8060511482402.8061170136174.7361254491452.7261305990311.6961423245358.9361519228526.716165337146.75 61778293102.7161917199008.9061917199020.7062145070432.7562145070444.7062302209411.7162302209411.9362343778002.716297249326.93 6299892651.92 63002572398.7563235321891.9163235321901.686326792124.71 63341493050.7564896830119.7565104334021.7865104452412.5 65666169454.7365769723580.7365805175866.6966094744694.9366330498732.7266330498734.7466554270958.7566571591084.8067284288444.7367471419575.7967777981223.9367800019075.7267800019075.946783195886.75 698988910.71  7130566823.71 7373603310.72 7600465283.73 7600465283.75 8405736896.93 8405736896.94 9099241916.73 945059608.79  00000500600700800900:00;00?00H00Q00Z00^00g01001901=01A01B01K01L01U01V01W01[01_01e01f01o02302802902:02C02H02I02M02V02W02X02Y02Z02[02d02e02j03303<03E03N03W03`03i04204;04?04C04L04P04Q04V04W04i04n05305705;05D05M05V05W05\05a05e05i06206;06?06L06Y06Z06[06d06i07207307707;07<07@07E07F07G07P07Y07_07c07g07h07i08208;08D08M08V08_08`08a08b08c08d08m09409;09H09U09b09i0:60:70:80:=0:F0:J0:K0:O0:S0:W0:`0:d0:e0:f0:o0;00;10;60;?0;@0;I0;J0;K0;T0;]0;f0<30<<0<E0<I0<J0<S0<\0<]0<^0<_0<`0<i0=20=;0=@0=A0=J0=S0=W0=[0=d0=h0>10>:0>C0>G0>K0>O0>X0>a0>j0?:0?;0?D0?H0?L0?M0?N0?]0?o0@30@70@;0@D0@H0@I0@R0@[0@`0@i0@m0A10A50A90A:0A;0AD0AM0AQ0AZ0A^0Ab0Af0Ak0Al0B90BF0BO0BS0BX0BY0B]0Ba0Bj0Bn0C20C70C80C90C:0CC0CL0CM0CV0CW0CX0CY0CZ0C^0C_S3SPRSSSSSSS2HBS4CEIL2LOS4CEIL2LOS4CEIL2LOS2HBS4CEIL2LOS4CEIL2LOS4CEIL2LOS2LOS2LOSS4CEIL2LOSS4CEIL2LOSSS2LOS2LOS4SPOSSS4CEIL2LOS2HBS3SPRSSS4CEIL2LOS3SPRSS2HBS4CEIL2LOSSSSSS4CEIL2LOSS3SPRS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS2LOS2LOS4CEIL2LOS2HBSS3SPRSS4CEIL2LO4SPOS3AM3S3SALS3SPRS2LOS2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSS3SPRS3SPRS2HBS2HBS4CEIL2LOS4CEIL2LOS2HBS4SPOS2A03ASZS4SPOS2A03ASZSSS4CEIL2LOS3SPRS4CEIL2LOSS2LOS2LOSS2LOS3SPRSSS4CEIL2LOS4CEIL2LOS2A01HS2LOS2LOSSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSSSSSS4CEIL2LOS2A02K1S2A02K1S4SPOS2A03ASZS4SPOS2A03ASZS4SPOS2A03AM3S2A02K1S4SPOS2A03AM3SSS3SPRS4CEIL2LOS2LOSS2HBS2LOS2LOS4CEIL2LOS2A0SSS4CEIL2LOSSS3SPRS4CEIL2LOSS4CEIL2LOSSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LO3AM3S4CEIL2LOS4CEIL2LOS2A0SS4CEIL2LOS4CEIL2LOSSSSS4CEIL2LOS4CEIL2LOS4CEIL2LOS3AALSS4CEIL2LOS4CEIL2LOS2LOS2LOS4CEIL2LOS2A0S4CEIL2LOS4CEIL2LOS4CEIL2LOS2LOS2LOS2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4SPOS3AM23AM31HSS4CEIL2LOS2LOS2LOSSS4SPOS3AM32LT1HS4SPOS3AM32K11H2K2S2HBS2A0S2LOS4CEIL2LOS2HBSS4CEIL2LOS4CEIL2LOS3SPRS4CEIL2LOS2LOS2LOS2LOS2LOSSS4CEIL2LOS4CEIL2LOS2LOS4CEIL2LOS2LOS2LOS2HBS3SPRSS4SPOS2A03AM3S4SPOS2A03ASZS4CEIL2LOS2HBS3SPRSS2LOS2LOS4CEIL2LOS2A0S2HBS3ASZSSSS4CEIL2LOS4CEIL2LOSS4CEIL2LOSSFFS2HBS".
carve_frame 96%nat ST.
  step. step. step. step. step. step. step.                    (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step. step. if_lit.                                          (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                                  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
  setreg 8 (Z_to_bv 64 size) ltac:(rewrite land_align4096 by lia; f_equal; clear -SAL SPOS ASZ A0; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  step. if_lit.                                                (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  setreg 18 (Z_to_bv 64 addr) ltac:(rewrite land_align4096 by lia; f_equal; clear -AAL A0 ASZ SPOS; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  step. step. step. step. step.                                (* [comment removed for export] *)
  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  carve_frame 272%nat ST.
  step. step. step. step. step. step. step. step.              (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  step. step. step. step. step. step. step. step. step.        (* [comment removed for export] *)
  release_frame FR0 ST (bv_unsigned sp + -96).
  step. setreg 13 (Z_to_bv 64 50) ltac:(vm_compute; reflexivity).   (* [comment removed for export] *)
  step. step. step. step. step.                                (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  (* [comment removed for export] *)
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
  replace (ret_pc (Z_to_bv 64 415436)) with (Z_to_bv 64 415436 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  apply (munch_weaken _ [(bv_unsigned sp - RMAPD_STACK, bv_unsigned sp); (addr, addr + size)]%Z) in MU.
  2: { unfold sub_fp. cbn [outside]. clear. intros x Hx. tauto. }
  sys_mem_zeros.
  (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step. step. step. if_cases K1; zify_cond K1. 2: { exfalso. clear -K1 AM3 SPOS A0. lia. }   (* [comment removed for export] *)
  zstep. step.                                                 (* [comment removed for export] *)
  setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 addr) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
  step. step. step. step. step. step.                          (* [comment removed for export] *)
  step. step. step. if_cases K2; zify_cond K2. 2: { exfalso. clear -K2 AM3 SPOS A0. lia. }
  zstep. step.
  setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 addr) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
  step. if_lit.                                                (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  step. step. step. step. if_lit. step.                        (* [comment removed for export] *)
  step. step. step. step. step. step. step. step. step.        (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -96) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  apply evtF_done. right. split; [reflexivity|].
  do 15 eexists. split. 2: reflexivity.
  unfold rmap_postD. destruct HF0 as [[FPLE _] [_ BW]].
  split; [exact FPLE|]. split; [exact AM3|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [exact ZNEW|]. split; [exact GR1|]. split; [exact GR2|]. split; [exact BW|].
  unfold rmap_cells. repeat (split; [assumption|]). assumption.
  Unshelve. all: apply ref_ro_addr_false; right; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC2.
