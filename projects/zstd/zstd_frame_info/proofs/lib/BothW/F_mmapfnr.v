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
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg AProto ABase AKit AKit2 RT_stubs F_ammap FsKit.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.
Definition AMMAPFNR : Z := 0x6d5cc.
Definition F_FIXNORES_RW_FLAGS : Z := 16434.       (* [comment removed for export] *)
End CANSEC1.
Notation FNR_STACK := 368 (only parsing).        (* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Definition fnr_cells (m : amem) : Prop :=
     rw_cells bsegs m 0x98ff0 [C8 (Z_to_bv 64 0x130ae0)]
  /\ rw_cells bsegs m 0x130ae0 [C8 (Z_to_bv 64 4096)]
  /\ rw_cells bsegs m 0x99000 [C8 (Z_to_bv 64 0x132b68); C8 (Z_to_bv 64 0x9e838); C8 (Z_to_bv 64 0xa1038);
                               C8 (Z_to_bv 64 0xa1d28); C8 (Z_to_bv 64 0xa1d30); C8 (Z_to_bv 64 0xa1d20)]
  /\ rw_cells bsegs m 0x132bf8 [C8 (Z_to_bv 64 0)].

#[using="Type"] Lemma fnr_cells_frame : forall m m' W, fnr_cells m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => AIMG_HI <= fst iv) W -> fnr_cells m'.
Proof.
  intros m m' W (R1 & R2 & R3 & R4) MU WM HW. unfold AIMG_HI in HW.
  assert (D : forall A k, 0 <= k -> A + k <= 0x5f6000 -> disjoint_from W A k).
  { clear -HW. intros A k Hk HA. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }
  unfold fnr_cells. repeat lazymatch goal with |- _ /\ _ => split end;
    (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn; apply D; lia]).
Qed.

Definition fnr_post (RNG : footprint) (sp : word) (addr size lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG'
  /\ munch [(bv_unsigned sp - FNR_STACK, bv_unsigned sp); (addr, addr + size)]%Z m m' /\ wmono bsegs m m'
  /\ mem_inv bsegs m'
  /\ stk bsegs m' lo (bv_unsigned sp)
  /\ rw_cells bsegs m' addr [CB (Z.to_nat size) (repeat (Z_to_bv 8 0) (Z.to_nat size))]
  /\ rng RNG' addr size
  /\ fp_bw RNG'
  /\ fnr_cells m'.

#[using="Type"] Lemma fnr_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size lo : Z) (junk : list byte),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - FNR_STACK ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 0 ->
  addr mod 4096 = 0 -> size mod 4096 = 0 -> 0 < size -> AIMG_HI <= addr -> addr + size <= 0x10007fff8000 ->
  fnr_cells m ->
  rw_cells bsegs m addr [CB (Z.to_nat size) junk] ->                 (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG addr size ->
  (* [comment removed for export] *)
  (forall a RNG' ms', a <> addr -> 0 < a -> a + size <= ATOP -> implS bsegs RNG' (K a) (epostF Q) ms') ->
  (forall RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      fnr_post RNG sp addr size lo m RNG' m' ->
      implS bsegs RNG' (K addr) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (ebind (enode (NMmap addr size 3 F_FIXNORES_RW_FLAGS) (adec_mmap ATOP size 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AMMAPFNR) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros ST CEIL LO MI -> -> -> AAL SAL SPOS A0 AHI RC DST RIMG RSTK RTGT UNR KONT. unfold AIMG_HI in A0.
  pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & GOT & MLIM).
  unfold AMMAPFNR, F_FIXNORES_RW_FLAGS in *. word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - FNR_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  eapply (implF_ebind _ _ _ _ _ _ _
            (fun a RNG' ms' => (a <> addr /\ 0 < a /\ a + size <= ATOP) \/ a = addr /\ exists m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
               fnr_post RNG sp addr size lo m RNG' m' /\
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom bsegs))).
  2: { intros a RNG' ms' [(NE & P1 & P2)|[-> PO]]; [apply UNR; [exact NE | exact P1 | exact P2]|].
       destruct PO as (m' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & PO & ->).
       eapply KONT. exact PO. }
  (* [comment removed for export] *)
  iprefix.
  Local Ltac2 Set LiaHints.tbl := fun () => "04;0>10667180602.791162083374.76 1164180523.94 11805467289.7111805467289.7311805467289.7411805467289.7511805467289.7611805467289.7711805467289.7911925506990.9512154650478.7712334040174.7312334040174.7513290116086.9414516788362.7914576153966.7714866570234.7715107956284.7915116433660.9515813913888.8015813913902.7816290529959.7617141182446.7117141182446.741772731779.77 1772731779.79 17776320428.7217778417576.9317976286208.2 1800609155.73 1800609155.94 18689773242.7718890355993.7718900419239.7919007305966.7419007305966.7719391258279.7719870165642.7420163737475.7520163737475.9520438143011.8320447870595.7920447870595.8121305031662.7921811810457.792190890265.77 22102740889.7922329023982.7922389541692.712350913305.77 23814431342.7323814431342.7524179267756.7624179267758.7824559830510.7424638473347.7424638473347.9525071629079.9525077027338.7725358857070.7325358857070.7525878270243.9225878270253.7326431752068.6 27066288442.7627136149358.7727408782893.7527408782895.7727785139628.8327907155234.8128125558140.8028370640551.7528417259964.7330023022247.7730231011258.773071671100.79 31378308326.6531929422315.7531940628442.6733065910700.8333680001082.7433680001082.7733875968138.7133875968138.7433962954137.7634122977177.7934285919648.7934285919662.7634417933740.7634417933741.7534430152252.743454500618.81 34924112163.7035082589626.7735190332526.7735205357699.7735205357699.9535482080238.7636106342346.7736107562391.8536113525291.9436115622447.7336320004846.7936590710439.7736637980185.7537827660420.6639571573379.7939571573379.8140089828523.9440091925676.7440133944238.9540150930599.7740287110510.7740457739452.7340527739801.7441116662894.7741272171651.7441272171651.9342085054489.7742236688921.7742501437472.9542503534630.7242505299482.6742511411968.8042511604512.8142511604641.8142817538363.8242995994990.7342995994990.7543059266230.6343243961582.794336735214.76 43985854248.9343987951407.7343988483203.7143988483203.934472014211.76 4472014211.77 44950045500.7745221239098.7445225660022.7945352467587.7945352467587.8145617101814.9445751589358.7145751589358.7445848756903.7146468661564.7446895624871.7946998232647.6847147249006.7747296502915.7647296502915.7848288466798.7748781039854.7448781039854.7749098903414.9449288693539.8349649769127.7449935451210.955012112366.74 50131542183.7550565006190.7350565006190.7550645511577.7950975666620.755098644739.95 51124399684.705120733337.76 51215735434.7651612993875.6 51678667180.7451680764331.9451711223320.8051952161006.7952035853038.7952105090727.735289276057.79 53424079911.9553767577772.7253769674920.9354242013742.7754243526019.7354243526019.9454788071470.7755015118318.7655207105262.7455207105262.775575378976.80 5575378990.78 55768096166.68563227834.73  563227834.75  56759370246.7 56779838332.6956986461756.7457269508355.7757269508355.8057697684362.7457697684362.7757745675194.7357745675194.75578361838.71  578361838.74  57897936679.7758762852128.8058762852142.7858776000537.7759028845166.7359028845166.7559055433134.9559314873579.7 59314873579.8 59370942190.7959758911548.795998835466.77 60084855288.8360280114806.9460511482531.816066363658.73 6066363658.75 60858483367.7461254491452.766165337146.79 61874979822.7461988516505.7963014048956.7563235321891.9263235321901.7063305555623.7363341493050.7964026414714.9564259584380.7764772824451.7564772824451.9564896830119.7964997134979.7464997134979.9465104334021.8165104450989.5 65129926126.7965673252078.7965769723580.7765845987594.7766330498732.7666330498734.7866794420697.7767284288444.7767323469228.8367471419575.8267696566282.7367696566282.7568393266841.777125526410.79 730490250.79  7486304935.74 7600465283.77 7600465283.79 8405736896.95 8583720762.71 8583720762.74 8772567833.75 9079110254.77 9099241916.77 9191764522.94 9309890606.77 00000500900=00>00?00@00A00B00C00D00M00V00_00h00i01;01D01I01M01Q01U01Y01Z01c01l01m01n02202602<02=02>02C02D02E02N02W02X02j02k02l03903:03;03D03E03F03G03P03T03U03^03g03k03o04804904:04;04M04V04_04c04g04l05105:05>05B05F05J05K05L05P05Q05V05Z05[05h06506906>06C06U06g06h06i06m07107507907=07>07B07G07P07Q07R07[07m08308708;08D08E08F08J08K08L08P08T08]08^08g08k08l09509609709809909@09M09Z09g09n0:;0:<0:E0:N0:R0:[0:d0:h0:l0:m0:n0:o0;00;40;90;:0;;0;<0;=0;F0;O0;P0;T0;U0;V0;_0;`0;a0;j0<30<<0<=0<J0<K0<]0<f0<g0=00=90=:0=>0=?0=@0=A0=S0=X0=\0=`0=a0=j0>30>40>50>60>:0>>0>G0>H0>I0>R0>[0>d0>m0?10?50?90?>0?C0?S0?T0?X0?Y0?Z0?l0@>0@C0@H0@Q0@Z0@[0@_0@c0@d0@m0A60A?0AN0A`0Ai0Am0B?0B@0BA0BE0BW0Bi0Bj0Bn0C30C<0C=0CA0CE0CI0CJ0CO0CT0CX0CY0CZ0C[0C\0C]0Cj0D70D@0DI0DM0D_0Dc0Dg0Dh0Dl0E00E50EG0EY0EZ0El0F>0F?0F@0FA0FB0FG0FL0FM0FV0FZ0F^0FgS3SPRS2LOS2LOSSSSSSSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSS4CEIL2LO4SPOS3AHIS4CEIL2LOS3SPRS2HBS2HBS2LOS2LOSS4CEIL2LOS4CEIL2LOSSS2LOS2LOS4SPOSSSS3SPRSSS4CEIL2LOS4CEIL2LOSS4CEIL2LO4SPOS3AHISSS4CEIL2LO3AHISSS4CEIL2LOSSSS4CEIL2LOS2HBSS4CEIL2LOS4CEIL2LOS2LOS2LOS4CEIL2LOSSSS4CEIL2LO4SPOS3AHIS4CEIL2LOS4CEIL2LOS2LOS2LOS3SALS3SPRS4CEIL2LOS2LOS2LOS2A0S2LOSSS2HBSS3SPRS2HBSS4SPOS2A03AHIS4SPOS2A03AHIS2A0S3SPRS3SPRS4CEIL2LO4SPOS3AHIS4CEIL2LO4SPOS3AHISSS2LOS2LOS2LOS2LOS2HBSS2LOS3SPRS4CEIL2LOSSS4CEIL2LOS4CEIL2LO4SPOS3AHIS2A01HS2LOS2LOS4CEIL2LOSSS2LOSSS2LOS2LOS4CEIL2LOSS4CEIL2LOS2HBSS4CEIL2LOSSSSS2A02K1S4SPOS2A03AHIS4SPOS2A03AHIS4SPOS2A03AHIS2A02K1S4SPOS2A03AHISS4CEIL2LOS4CEIL2LOS2LOS4CEIL2LOS4CEIL2LOS2LOS2LOSSSSS2HBS3SPRSSSSS4CEIL2LOS4CEIL2LOSS2HBSSS4CEIL2LOSSS4CEIL2LOS4CEIL2LOS4CEIL2LOSS4CEIL2LO3AHISS4CEIL2LO4SPOS3AHIS4CEIL2LOSS4CEIL2LOS4CEIL2LOSS2HBSSSS4CEIL2LO4SPOS3AHIS3AALS2LOS2LOSS4CEIL2LOS4CEIL2LOSSSS2LOS2LOS4CEIL2LOSSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS2LOS2LOS2LOS3SPRS3SPRS4SPOS3AM23AM31HSS2HBSSS4CEIL2LO4SPOS3AHIS4CEIL2LO4SPOS3AHIS3SPRS3SPRS4CEIL2LOS4CEIL2LOSS2LOS2LOSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4SPOS3AM32LT1HS4SPOS3AM32K11H2K2S4CEIL2LOS2HBS4CEIL2LO4SPOS3AHIFSS2LOS4CEIL2LO4SPOS3AHIS4CEIL2LO4SPOS3AHISS2HBS3SPRS4CEIL2LOSS2HBS2LOS2LOSS3SPRS3SPRS2HBSSSSSS4SPOS2A03AHIS4SPOS2A03AHIS4CEIL2LOS4CEIL2LOS2HBS4CEIL2LO4SPOS3AHIS2LOS2LOSS2HBS2A0S3AHIS4CEIL2LO4SPOS3AHIS4CEIL2LO4SPOS3AHISS4CEIL2LO4SPOS3AHIS4CEIL2LO4SPOS3AHISSSFS3SPRS3SPRSS4CEIL2LOS2HBS2LOS4CEIL2LO".
carve_frame 48%nat ST.
  do 6 step.                                                   (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step. step. if_lit.                                          (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                                  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
  setreg 8 (Z_to_bv 64 size) ltac:(rewrite land_align4096 by lia; f_equal; clear -SAL SPOS AHI A0; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  step. if_lit.                                                (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  setreg 18 (Z_to_bv 64 addr) ltac:(rewrite Z.land_comm, land_align4096 by lia; f_equal; clear -AAL A0 AHI SPOS; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  step. step. step. step. step. step.                          (* [comment removed for export] *)
  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  carve_frame 48%nat ST.
  do 5 step.                                                   (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  carve_frame 272%nat ST.
  do 8 step.                                                   (* [comment removed for export] *)
  step. step. step. if_lit.                                    (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  do 9 step.                                                   (* [comment removed for export] *)
  release_frame FR1 ST (bv_unsigned sp + -96).
  step. setreg 13 (Z_to_bv 64 16434) ltac:(vm_compute; reflexivity).   (* [comment removed for export] *)
  step. step. step. step. step.                                (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  icallk rt_mmap_stubP.
  intros a RNG' ms' (rsp & HF & Hdec & ->).
  destruct (adec_mmap_rw_Some _ _ _ Hdec) as (ci & -> & AM1 & AM2 & AM3).
  pose proof (page_round_up_mult size SAL ltac:(clear -SPOS; lia)) as PRU. unfold mmap_len in *. rewrite PRU in AM3. rewrite PRU.
  pose proof (fstepA_mmap_grant addr size 16434 _ RNG RNG' (fstepS_fstepA _ _ _ _ HF)) as GR. cbn [eff_ret] in GR.
  rewrite (unsigned_lit a) in GR by (clear -AM2 AM3 SPOS; lia). rewrite (unsigned_lit size) in GR by (clear -SPOS AHI A0; lia).
  rewrite PRU in GR. specialize (GR ltac:(unfold page_size; exact AM1)).
  pose proof HF as HF0. fstepS_transport HF.
  destruct (Z.eq_dec a addr) as [->|NE]. 2: { apply evtF_done. left. split; [exact NE|]. split; [exact AM2| atop_facts; exact AM3]. }
  unfold rt_regs. cbn [eff_ret]. rewrite eff_mem_zeros.
  replace (ret_pc (Z_to_bv 64 0x65134)) with (Z_to_bv 64 0x65134 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  apply (munch_weaken _ [(bv_unsigned sp - FNR_STACK, bv_unsigned sp); (addr, addr + size)]%Z) in MU.
  2: { unfold sub_fp. cbn [outside]. clear. intros x Hx. tauto. }
  sys_mem_zeros.
  (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step. step. step. if_cases K1; zify_cond K1. 2: { exfalso. clear -K1 AM3 SPOS A0. lia. }   (* [comment removed for export] *)
  zstep. step.                                                 (* [comment removed for export] *)
  setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 addr) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
  step.                                                        (* [comment removed for export] *)
  step. step. step. step. step. step.                          (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -96) _, STK : stk bsegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp + -48) end.
  (* [comment removed for export] *)
  step. step. step. step. step.                                (* [comment removed for export] *)
  step. step. step. if_cases K2; zify_cond K2. 2: { exfalso. clear -K2 AM3 SPOS A0. lia. }
  zstep. step.
  setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 addr) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
  step. step. if_lit.                                          (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  step. step. step. step. if_lit. step.                        (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  step. step. step. step. step. step. step.                    (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -48) _, STK : stk bsegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  apply evtF_done. right. split; [reflexivity|].
  do 15 eexists. split. 2: reflexivity.
  unfold fnr_post. destruct HF0 as [[FPLE _] [_ BW]].
  split; [exact FPLE|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [exact ZNEW|]. split; [exact GR|]. split; [exact BW|].
  unfold fnr_cells. repeat (split; [assumption|]). assumption.
  Unshelve. all: apply ref_ro_addr_false; right; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC2.
