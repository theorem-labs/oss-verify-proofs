(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import MM_syscalls.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import SysStepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg AProto ABase AKit AKit2 RT_stubs F_ammap.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition mmapz_entry := 0x651d8.
End CANSEC1.
Notation MMAPZ_STACK := 320 (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Definition mmapz_post (RNG : footprint) (sp : word) (a size lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG' /\ fp_bw RNG'
  /\ a mod 4096 = 0 /\ 0 < a /\ a + size <= ATOP
  /\ munch [(bv_unsigned sp - MMAPZ_STACK, bv_unsigned sp); (a, a + size)]%Z m m' /\ wmono bsegs m m'
  /\ mem_inv bsegs m'
  /\ stk bsegs m' lo (bv_unsigned sp)
  /\ rw_cells bsegs m' a [CB (Z.to_nat size) (repeat (Z_to_bv 8 0) (Z.to_nat size))]
  /\ rng RNG' a size /\ rng RNG' (shad a) (shlen size)
  /\ rmap_cells m'.

#[using="Type"] Lemma mmapz_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    (FRESH : Z -> bool)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (size lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - MMAPZ_STACK ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 size -> size mod 4096 = 0 -> 0 < size -> size < 2^40 -> bv_unsigned a1 <> 0 ->
  rmap_cells m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  (forall a, FRESH a = true -> 0 < a -> a + size <= ATOP -> AIMG_HI <= a /\ (a + size <= bv_unsigned sp - 48 \/ bv_unsigned sp <= a)) ->
  (* [comment removed for export] *)
  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + size <= ATOP -> fp_le RNG RNG' ->
      implS bsegs RNG' (K a) (epostF Q) ms') ->
  (* [comment removed for export] *)
  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> mmapz_post RNG sp a size lo m RNG' m' ->
      implS bsegs RNG' (K a) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 a) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (ebind (enode (NMmap 0 size 3 34) (adec_mmap ATOP size 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 mmapz_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> SAL SPOS SZ NAME RC RIMG RSTK FROK UNR KONT.
  pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & GOT & DPM & MLIM). word_range a1 A1R.
  unfold AIMG_HI, mmapz_entry in *. word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - MMAPZ_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  eapply (implF_ebind _ _ _ _ _ _ _
            (fun a RNG' ms' => (FRESH a = false /\ 0 < a /\ a mod 4096 = 0 /\ a + size <= ATOP /\ fp_le RNG RNG')
                            \/ FRESH a = true /\ exists m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
               mmapz_post RNG sp a size lo m RNG' m' /\
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 a) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom bsegs))).
  2: { intros a RNG' ms' [(NF & P1 & P2 & P3 & P4)|[FR PO]]; [apply UNR; assumption|].
       destruct PO as (m' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & PO & ->).
       eapply KONT; [exact FR | exact PO]. }
  (* [comment removed for export] *)
  iprefix.
  Local Ltac2 Set LiaHints.tbl := fun () => "0320?10057101576.89 10667180602.78 10873507702.10211613226300.77 1162083360.80  1162083374.77  11805467289.72 11805467289.74 11805467289.75 11805467289.76 11805467289.77 11805467289.78 12119712956.76 12154650478.76 12334040174.74 13380609710.74 14576153966.76 14866570234.74 15061177992.89 16540621984.79 16540621996.73 17141182446.72 17776320428.73 17778417576.10117976286208.2  1800609155.102 1800609155.74  18689773242.75 19007305966.75 21305031662.78 21811810457.78 2190890265.76  22219720579.76 22219720579.79 22329023982.78 22389541692.72 22795432430.74 22885694752.70 23063337974.79 2350913305.76  23814431342.74 24468186791.76 24487705898.71 24559830510.10224559885228.75 24559885230.78 24638473347.10224676552814.75 24974828534.10225071629079.10225358857070.74 25878270253.74 25878270255.77 26015742015.89 26034797806.76 26429361813.4  27066288442.75 27136149358.76 27408782881.79 27408782895.76 27907155234.89 28046884974.10228417259964.74 29448452775.76 30231011258.76 31378308326.66 31764313966.77 31929422314.77 31940628442.68 32300784295.78 32501562499.78 32501562499.81 33468360968.89 33680001082.75 33890036512.80 33890036526.77 33962954137.75 34122977177.78 34430152252.75 35082589626.76 35100153219.75 35100153219.76 35190332526.75 35482080238.75 36107562391.92 36320004846.78 37827660420.67 38534813827.75 38534813827.78 39058966403.76 39058966403.79 39130834926.75 40091925677.74 40091925677.75 40287110510.76 40333419028.88 40457739452.74 41116662894.75 41140841326.75 4288869222.89  42995994990.74 43059266230.64 43158752138.87 43243961582.77 4336735214.75  43985854248.10143987951407.74 43988483203.10143988483203.72 44223460412.78 44464229507.78 44464229507.81 45221239098.10245617101814.10145751589358.72 45848756903.72 46382356647.75 46468661564.10247147249006.76 4751458172.69  48288466798.76 48781039854.75 49649769127.75 49725372071.75 5012112366.102 50244754108.76 50565006190.74 51509148455.74 51678667180.75 51678667182.78 51711223320.88 51952161006.78 52035853038.78 52105090727.74 53767577772.73 53769674920.10154242013742.74 54243526019.10254243526019.74 54788071470.74 55015118318.75 55207105262.75 56241442027.10156255680316.78 563227834.74   56457031918.74 56759370246.7  56763417884.86 56765693756.89 56765693885.88 56771238972.10256771238972.10357745675194.74 578361838.72   58776000537.75 59028845166.74 59308628179.4  59314873579.7  59370942190.77 60537240323.74 60537240323.80 6085061230.72  60858483367.1026094239292.75  6165337146.77  61874979822.10261988516505.77 62283267516.75 6320660206.76  63235321891.10063235321901.71 63305555623.74 63341493050.78 64997134979.10264997134979.75 65104334021.87 65106320572.3  65129926126.78 65417393774.78 65673252078.77 65704139943.77 66021542019.77 66021542019.80 67134106962.10267579755272.89 67643606599.69 7735119015.78  8405736896.102 8405736896.103 8583720762.72  9079110254.75  9107720828.74  9309890606.74  9802357102.78  00000500:00;00?00C00G00H00I00J00K00L00M00Q00Z00c00l01501:01?01C01G01P01T01X01^01_01`01e01n02702802902:02;02D02H02Q02U02V02W02`02a02b02k02o03303403=03>03?03H03L03P03]03f03k04004904=04A04E04N04R04S04X04Y04b04k05405505605705<05A05E05I05J05K05O05T05U05V05_05h05o06806<06=06>06?06@06I06M06Q06Z06_06c06l07507607?07C07D07M07V07Z07^07_07`07d07e07f07k07l08508608708;08D08E08N08W08X08Y08b08f08o09009409809909B09K09L09P09T09]09^09_09h0:10::0:>0:B0:G0:P0:`0:n0;60;D0;L0;T0;Y0;b0;c0;l0<90<N0<W0<X0<Y0<b0<c0<g0<l0=50=60=:0=C0=G0=K0=L0=Q0=R0=S0=\0=e0=n0>70>@0>A0>B0>C0>U0>Z0>[0>\0>]0>^0>c0>l0?00?90?BS3AIMS3SPRSS2HBS2LOS2LOSSSSSSS2HBS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS3SPRS3AIMS2LOS2LOS4CEIL2LOS2LOS2LOS4SPOSSSS3SPRS4CEIL2LOS4CEIL2LOSSSSS4CEIL2LOS2HBS4CEIL2LOS2LOSSS4CEIL2LOSSS4CEIL2LOS2LOS2LOSS4CEIL2LOSSS4CEIL2LOS2LOS2LOS4CEIL2LO3AM3S4CEIL2LOS3SALS3SPRS4CEIL2LOS2LOS2LOS2LOS4CEIL2LOS2HBSS3SPRSS4CEIL2LOS4SPOS2SZS4SPOS2SZSSSS3AIMS3SPRS2LOS2LOSSS2HBS3SPRSSS4CEIL2LOS4CEIL2LOS3AIM1HS4CEIL2LOS2LOSSSSS4CEIL2LOS2LOS2LOS4CEIL2LOS3AM3S2HBS4CEIL2LOS4CEIL2LOSS4CEIL2LOS2LOSS4CEIL2LOS4CEIL2LOS2LOS2LOSSS2HBSSS3SPRSS4CEIL2LOSSS2HBS4CEIL2LOSS4CEIL2LOS4CEIL2LOSSS4CEIL2LOS2HBS4CEIL2LOSS2LOS2LOSS4CEIL2LOS4CEIL2LOSS2LOS2LOS4CEIL2LOSSS4CEIL2LOS4CEIL2LOS4CEIL2LOS2LOS2HBS3SPRS4CEIL2LOS4SPOS3AM23AM31HS4SPOS3AM23AM3S3AM22K1S4SPOS3AM23AM3S3AM22K1S3AM22K1S3SPRS4CEIL2LOSS4CEIL2LOS4NAME3A1R2K0S4SPOS3AM32K11H2LT2K2S4CEIL2LOSSS4CEIL2LOSS2HBS3SPRS4CEIL2LOSS2HBS4CEIL2LOS2LOS2LOSS3SPRSSS4SPOS2SZS4SPOS2SZS4CEIL2LOS4CEIL2LOS4CEIL2LOSSSS4CEIL2LO4SPOS3AM3S3AIMSSFFS3SPRS4CEIL2LOS2HBS4CEIL2LOS4CEIL2LO".
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
  replace (ret_pc (Z_to_bv 64 414304)) with (Z_to_bv 64 414304 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
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
  lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -48) _, STK : stk bsegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
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
Definition rmapd_entry := 0x6d9a8.
#[using="Type"] Lemma rmapd_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RMAPD_STACK ->
  mem_inv bsegs m ->
  a1 = Z_to_bv 64 addr -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 0 ->
  addr mod 4096 = 0 -> size mod 4096 = 0 -> 0 < size -> AIMG_HI <= addr -> addr + size < 2^63 ->
  rmap_cells m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  (forall a RNG' ms', a <> addr -> 0 < a -> a + size <= ATOP -> implS bsegs RNG' (K a) (epostF Q) ms') ->
  (forall RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      rmap_postD RMAPD_STACK RNG sp addr size lo m RNG' m' ->
      implS bsegs RNG' (K addr) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (ebind (enode (NMmap addr size 3 50) (adec_mmap ATOP size 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rmapd_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> -> -> AAL SAL SPOS A0 ASZ RC RIMG RSTK UNR KONT. unfold AIMG_HI in A0.
  pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & GOT & DPM & MLIM).
  unfold rmapd_entry in *. word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - RMAPD_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  eapply (implF_ebind _ _ _ _ _ _ _
            (fun a RNG' ms' => (a <> addr /\ 0 < a /\ a + size <= ATOP) \/ a = addr /\ exists m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
               rmap_postD RMAPD_STACK RNG sp addr size lo m RNG' m' /\
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom bsegs))).
  2: { intros a RNG' ms' [(NE & P1 & P2)|[-> PO]]; [apply UNR; [exact NE | exact P1 | exact P2]|].
       destruct PO as (m' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & PO & ->).
       eapply KONT. exact PO. }
  (* [comment removed for export] *)
  iprefix.
  step. step. step. step.                                      (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  Local Ltac2 Set LiaHints.tbl := fun () => "03I0>10667180602.7511805467289.6911805467289.7111805467289.7211805467289.7311805467289.75118736110.72  12154650478.7312352412732.7214576153966.7315107956284.7515813913888.7615813913902.7416033677678.7116290529959.7217151130279.721772731779.73 1772731779.75 17776320428.7017778417576.9217976286208.2 17995455655.7118363204284.7118689773242.7318890355993.7318900419239.7519179019630.7219376804346.9319391258279.7319625521020.9319970277031.7120292650734.6920447870595.7520447870595.7721220757366.932124193155.71 2124193155.91 21305031662.7522102740889.7522163107130.7222329023982.7524179267756.7224179267758.7424390924092.6924409718067.7124630998586.7224676552814.7225071629079.9325099790446.7125223810670.7126034797806.7326115614154.9326431752469.6 26816462382.9327066288442.7227136149358.7327408782893.7127408782895.7327785139628.8030023022247.7330196181434.7130231011258.7330403814844.713071671100.75 315996476.72  31764313966.7531929422315.7331940628442.6532127996803.7132127996803.9332651489978.7133065910700.8034417933740.7234417933741.7134570277878.9334924112160.6635082589626.7335111703823.7135111703823.7635190332526.7335482080238.7235567461870.7136015289582.6936107562391.8336113525291.9336115622447.7136180999398.6336320004846.7536590710439.7339130834926.7339571573379.7539571573379.7740287110510.7340629668746.7840818930798.7241116662894.734182447342.69 42085054489.7342236688921.7342501437472.9342501437472.9442503534630.7042505299482.6542509314849.7742511604512.8042511604641.7942775782659.9342817538363.8042831019478.7143059266230.6143243961582.754336735214.72 4339538087.72 43413664432.7143985854248.9243987951407.714472014211.72 4472014211.73 45352467587.7545352467587.7746232973498.7146827545646.9346895624871.7547147249006.7347296502915.7247296502915.7448288466798.7348498465782.7549119731694.7249288693539.804932169326.71 50645511577.7551124399687.665114850435.72 5114850435.93 5120733337.72 51612993474.6 5191233902.71 51952161006.7552035853038.755289276057.75 53767577772.7053769674920.9253906595694.6954011733842.7155015118318.725575378976.76 5575378990.74 55770193284.6456199689966.7256759370246.7 56779838332.6558360670702.7258536729426.7158762852128.7658762852142.7458906746862.7259190426614.9259192637571.6959192637571.9259314873579.7 59314873579.8 59370942190.7559748865774.7259758911548.7560138129582.9360277639852.8060511482402.8060679622738.7161254491452.7261305990311.696165337146.75 61917199008.9061917199020.7062091965166.7162145070432.7562145070444.7062302209411.7162302209411.936299892651.92 63174103918.716320660206.73 63235321891.9163235321901.686326792124.71 63341493050.7564398247470.9364556005486.7164758730450.7164896830119.7565104334021.7865104452412.5 65129926126.7565417393774.7565673252078.7565769723580.7365805175866.6966330498732.7266330498734.7466443298926.7167284288444.7367323469228.8067471419575.7967777981223.9367800019075.7267800019075.947130566823.71 7600465283.73 7600465283.75 831511534.71  8405736896.93 8405736896.94 8989589102.71 9079110254.73 9099241916.73 945059608.79  9802357102.75 00000500600700800900:00C00L00P00Y00]00a00e00n00o01001101201601:01@01A01E01J01K01L01U01Z01[01_01`01i01j01k01l01m01n02702802=02F02J02N02R02S02X02a02b02k03403=03O03T03]03b03k03o04304704804=04B04F04J04N04W04d05105205305805<05@05D05E05I05N05O05P05Y05b05k06406:06>06B06C06L06M06V06W06X06a06b06k07407=07>07?07F07M07Z07g08408;08H08I08J08O08S08\08e08f08j08n09209309409509609;09D09E09N09O09P09Y09Z09c0:00:90::0:;0:<0:=0:>0:C0:L0:U0:^0:_0:c0:g0;00;90;B0;F0;J0;N0;W0;g0;h0<10<:0<>0<B0<K0<L0<M0<N0<]0<o0=80=A0=E0=N0=R0=V0=_0=c0=d0=i0=m0>10>:0>>0>B0>C0>D0>H0>Q0>Z0>^0>b0>f0>k0?40?=0?F0?G0?T0?a0?j0@30@<0@@0@E0@I0@M0@V0@Z0@^0@c0@d0@e0@f0@g0@h0@i0A20A30A40A=0AF0AJ0AK0ATS3SPRSSSSSS4CEIL2LOS4CEIL2LOS2HBS4CEIL2LOS2HBS2LOS2LOS4CEIL2LOSSSSS2LOS2LOS4SPOSSS2HBS3SPRSSS4CEIL2LOS3SPRSS2HBSS4CEIL2LOSSSSSS4CEIL2LOSS3SPRS4CEIL2LOS2LOS2LOS2HBSS3SPRS4CEIL2LOSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LO4SPOS3AM3S3SALS4CEIL2LOS3SPRS4CEIL2LOS2LOS2LOS2A0SS3SPRS3SPRS2HBS2HBS2HBS4CEIL2LOS4SPOS2A03ASZS4SPOS2A03ASZSSS3SPRS2A0S2LOS2LOSS2LOS3SPRSSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS2A01HS2LOS2LOSS4CEIL2LOSS4CEIL2LOSSS4CEIL2LOSS4CEIL2LOS4CEIL2LOS4CEIL2LOSSS2A02K1S2A02K1S4SPOS2A03ASZS4SPOS2A03ASZS4SPOS2A03AM3S2A02K1S4SPOS2A03AM3SSS3SPRS2LOS4CEIL2LOS4CEIL2LOSS2HBS2LOS2LOSSSSS3SPRS4CEIL2LOSS4CEIL2LOSSS4CEIL2LOSS4CEIL2LOS4CEIL2LO3AM3S4CEIL2LOSSSSSS3AALS4CEIL2LOS4CEIL2LOS4CEIL2LOSS2LOS2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS2LOS2LOS2LOS4CEIL2LOS4SPOS3AM23AM31HSS4CEIL2LOS4CEIL2LOS2LOS2LOS4CEIL2LOSSSS4SPOS3AM32LT1HS4SPOS3AM32K11H2K2S4CEIL2LOS4CEIL2LOS2HBS4CEIL2LOS2A0S2LOS4CEIL2LOS2HBSS3SPRS2LOS2LOS4CEIL2LOS2LOS2LOSSS2LOS4CEIL2LOS4CEIL2LOS2LOS2LOS2HBS3SPRS4CEIL2LOS4CEIL2LOS4CEIL2LOSS4SPOS2A03AM3S4SPOS2A03ASZS4CEIL2LOS4CEIL2LOS4CEIL2LOS2HBS3SPRS2LOS2LOS4CEIL2LOS2HBS2A0S3ASZSSSSSSS4CEIL2LOFFS4CEIL2LOS4CEIL2LOS2HBSS4CEIL2LO".
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
  replace (ret_pc (Z_to_bv 64 415440)) with (Z_to_bv 64 415440 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
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
  lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -96) _, STK : stk bsegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
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
