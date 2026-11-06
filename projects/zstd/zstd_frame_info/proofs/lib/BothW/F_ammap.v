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
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg AProto ABase AKit AKit2 RT_stubs.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition rmap_entry := 0x6d85c.
End CANSEC1.
(* [comment removed for export] *)
Notation RMAP_STACK := 400 (only parsing).   (* [comment removed for export] *)
Notation RMAPD_STACK := 368 (only parsing).  (* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Definition rmap_cells (m : amem) : Prop :=
     rw_cells bsegs m 0x98ff0 [C8 (Z_to_bv 64 0x130ae0)]
  /\ rw_cells bsegs m 0x130ae0 [C8 (Z_to_bv 64 4096)]
  /\ rw_cells bsegs m 0x99000 [C8 (Z_to_bv 64 0x132b68); C8 (Z_to_bv 64 0x9e838); C8 (Z_to_bv 64 0xa1038);
                               C8 (Z_to_bv 64 0xa1d28); C8 (Z_to_bv 64 0xa1d30); C8 (Z_to_bv 64 0xa1d20)]
  /\ rw_cells bsegs m 0x132c6c [C1 (Z_to_bv 8 0)]
  /\ rw_cells bsegs m 0x132bf8 [C8 (Z_to_bv 64 0)].

#[using="Type"] Lemma rmap_cells_frame : forall m m' W, rmap_cells m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => AIMG_HI <= fst iv) W -> rmap_cells m'.
Proof.
  intros m m' W (R1 & R2 & R3 & R4 & R5) MU WM HW. unfold AIMG_HI in HW.
  assert (D : forall A k, 0 <= k -> A + k <= 0x5f6000 -> disjoint_from W A k).
  { clear -HW. intros A k Hk HA. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }
  unfold rmap_cells. repeat lazymatch goal with |- _ /\ _ => split end;
    (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn; apply D; lia]).
Qed.

(* [comment removed for export] *)
Definition rmap_postD (D : Z) (RNG : footprint) (sp : word) (addr size lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG'
  /\ addr + size <= ATOP
  /\ munch [(bv_unsigned sp - D, bv_unsigned sp); (addr, addr + size)]%Z m m' /\ wmono bsegs m m'
  /\ mem_inv bsegs m'
  /\ stk bsegs m' lo (bv_unsigned sp)
  /\ rw_cells bsegs m' addr [CB (Z.to_nat size) (repeat (Z_to_bv 8 0) (Z.to_nat size))]
  /\ rng RNG' addr size /\ rng RNG' (shad addr) (shlen size)
  /\ fp_bw RNG'                                   (* [comment removed for export] *)
  /\ rmap_cells m'.
Definition rmap_post := rmap_postD RMAP_STACK.

#[using="Type"] Lemma page_round_up_mult : forall s, s mod 4096 = 0 -> 0 <= s -> page_round_up_Z s = s.
Proof. intros s Hs H0. unfold page_round_up_Z, page_size. Z.div_mod_to_equations. nia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma land_align4096 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709547520 = x - x mod 4096.
Proof.
  intros x Hx.
  replace 18446744073709547520 with (Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity.
  replace (x - x mod 4096) with (Z.shiftl (Z.shiftr x 12) 12).
  2:{ Local Ltac2 Set LiaHints.tbl := fun () => "0080=10351595562.517210504373.517210506534.319456077695.735497642613.554865026814.356093574452.79074610895.7 00000400500600900:00;00B00FS2HiSSS1LSSS2Hx2NZS2Hx".
rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^12) with 4096. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  rewrite <- Z.ldiff_ones_r by lia.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !Z.ldiff_spec, !Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec i 64) as [L|L]; cbn.
  - reflexivity.
  - destruct (Z.eq_dec x 0) as [->|NZ]. { rewrite Z.bits_0. reflexivity. }
    rewrite (Z.bits_above_log2 x i); [reflexivity| lia |].
    apply Z.lt_le_trans with 64; [|lia]. apply Z.log2_lt_pow2; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma land_align2p18 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709289472 = x - x mod 262144.
Proof.
  intros x Hx.
  replace 18446744073709289472 with (Z.ldiff (Z.ones 64) (Z.ones 18)) by reflexivity.
  replace (x - x mod 262144) with (Z.shiftl (Z.shiftr x 18) 18).
  2:{ Local Ltac2 Set LiaHints.tbl := fun () => "0080=10351595562.519456077695.719939214485.519939216646.335497642613.554865026814.356093574452.79074610895.7 00000400700800900:00;00B00FS2HiS1LSSSSS2Hx2NZS2Hx".
rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^18) with 262144. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  rewrite <- Z.ldiff_ones_r by lia.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !Z.ldiff_spec, !Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec i 64) as [L|L]; cbn.
  - reflexivity.
  - destruct (Z.eq_dec x 0) as [->|NZ]. { rewrite Z.bits_0. reflexivity. }
    rewrite (Z.bits_above_log2 x i); [reflexivity| lia |].
    apply Z.lt_le_trans with 64; [|lia]. apply Z.log2_lt_pow2; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma adec_mmap_rw_Some : forall len rsp a, adec_mmap ATOP len 3 rsp = Some a ->
  exists ci, rsp = mkEffectU (Z_to_bv 64 a) [] [(wa a, Z_to_bv 64 (mmap_len len))] [] [] ci
          /\ a mod 4096 = 0 /\ 0 < a /\ a + mmap_len len <= ATOP.
Proof.
  intros len rsp a H. unfold adec_mmap in H. cbn [Z.eqb] in H.
  destruct (dec_mmap ATOP len [] rsp) as [[e|a']|] eqn:D; try discriminate. injection H as <-.
  destruct (dec_mmap_Some _ _ _ _ _ D) as [ci [E OK]]. exists ci. split; [exact E|].
  pose proof (mmap_addr_ok_true _ _ _ _ OK) as [(M1 & M2 & M3) _]. unfold page_size in M1. auto.
Qed.

#[using="Type"] Lemma rmap_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RMAP_STACK ->
  mem_inv bsegs m ->
  a1 = Z_to_bv 64 addr -> a2 = Z_to_bv 64 size -> 0x10000 <= bv_unsigned a3 < 2^47 ->
  addr mod 4096 = 0 -> size mod 4096 = 0 -> 0 < size -> AIMG_HI <= addr -> addr + size < 2^63 ->
  rmap_cells m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  (forall a RNG' ms', a <> addr -> 0 < a -> a + size <= ATOP -> implS bsegs RNG' (K a) (epostF Q) ms') ->
  (forall RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      rmap_post RNG sp addr size lo m RNG' m' ->
      implS bsegs RNG' (K addr) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (ebind (enode (NMmap addr size 3 50) (adec_mmap ATOP size 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rmap_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> -> NAME AAL SAL SPOS A0 ASZ RC RIMG RSTK UNR KONT. unfold AIMG_HI in A0.
  pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & GOT & DPM & MLIM).
  unfold rmap_entry in *. word_range sp SPR. word_range a3 A3R.
  pose proof (munch_refl [(bv_unsigned sp - RMAP_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  eapply (implF_ebind _ _ _ _ _ _ _
            (fun a RNG' ms' => (a <> addr /\ 0 < a /\ a + size <= ATOP) \/ a = addr /\ exists m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
               rmap_post RNG sp addr size lo m RNG' m' /\
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom bsegs))).
  2: { intros a RNG' ms' [(NE & P1 & P2)|[-> PO]]; [apply UNR; [exact NE | exact P1 | exact P2]|].
       destruct PO as (m' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & PO & ->).
       eapply KONT. exact PO. }
  (* [comment removed for export] *)
  iprefix.
  (* [comment removed for export] *)
  Local Ltac2 Set LiaHints.tbl := fun () => "04S0?10439767981.76 10439767981.77 10667180602.80 10835893820.80 1162083374.77  1164180522.100 11805467289.72 11805467289.73 11805467289.74 11805467289.75 11805467289.76 11805467289.77 11805467289.78 11805467289.79 11805467289.80 11833462140.99 118736110.78   12017784537.99 12154650478.78 12334040174.74 12866317849.78 13084834179.78 13084834179.81 13725786656.82 13725786670.79 14576153966.78 15062336688.76 15685060272.73 16033677678.76 16781328285.76 16844590268.77 17221588796.72 17776320429.72 17778417576.98 17976286208.2  18689773242.77 19006120615.75 19007305966.72 19179019630.78 19376804346.99 19491992743.75 20289765031.77 20292650734.75 21220757366.99 21305031662.80 21931701891.80 21931701891.83 22080489625.78 22163107130.78 22329023982.80 22439364775.76 22795432430.74 22872305980.80 23230285244.74 23814431342.74 23909860377.78 24080369177.78 24179267756.77 24179267758.80 24487705898.73 24559830510.75 24630998586.78 24676552814.77 25029166211.10125029166211.78 25071629079.99 25099790446.76 25117511228.78 25223810670.76 25435258127.73 25435258127.99 25566553219.75 25566553219.99 25876173099.99 25878270254.77 26000888601.77 26034797806.78 26115614154.99 26278908583.76 26431752469.6  26816462382.99 26868428163.76 26868428163.98 27066288442.77 27136149358.78 27679091076.67 27785139628.86 28046884974.75 28885198780.78 29515017603.77 29515017603.78 30196181434.76 30231011258.78 30518562691.10030518562691.76 31143001276.76 31193132057.78 31420974624.72 31764313966.79 31929422315.78 31940628442.70 32651489978.76 32905389884.77 33065910700.86 33342412455.78 33680001082.72 34288016811.98 34290115814.66 34570277878.99 35082589626.78 35190332526.77 3520940321.81  3520940335.78  35482080238.77 35567461870.76 35677373209.76 36015289582.75 36107562391.89 36115622435.97 36115622445.74 36320004846.80 36367760551.78 37044431129.77 37153923388.75 38806986883.72 38806986883.98 38916199868.78 39130834926.77 39939624357.86 40091925667.97 40091925676.75 40259044249.79 40287110510.78 40629668746.84 40818930798.78 40987550979.99 41116662894.77 41140841326.72 41564619544.85 4182447342.75  4240063612.85  42501437472.10042501437472.99 42503534630.75 42505299482.70 42509314849.83 42511603879.86 42511604512.86 42511604641.85 42817538363.86 42831019478.73 42831019478.76 43059266230.64 43183609788.76 43231650947.80 43231650947.83 43243961582.79 4336735214.77  43466089753.76 43985854248.98 43987951407.74 44158664835.75 44158664835.98 44621604505.77 45221239098.75 46232973498.76 46556098215.78 46690875510.99 46707059850.86 46827545646.99 47147249006.78 47373904281.79 48288466798.78 48355031171.77 48355031171.80 48498465782.81 48781039854.72 49119731694.78 4932169326.76  5012112366.75  50215255347.76 50862133932.77 50862133934.80 50882889347.79 50882889347.82 51612993474.6  51678667180.75 51680764331.99 5180980284.75  5191233902.76  51933874855.78 51952161006.80 52035853038.80 53324805799.79 53618414247.80 53767577772.73 53769674920.98 53906595694.75 54011733842.73 54011733842.76 54148288295.99 54618151079.74 55015118318.77 55104759171.74 55104759171.99 55207105262.72 55467843644.79 55681940633.77 5575378989.76  5575378991.79  55837769369.80 56199689966.78 563227834.74   56759370246.7  56993697826.86 5745572519.80  57756175257.80 58360670702.78 58536729426.73 58536729426.76 58655119491.10058655119491.78 58762852128.82 58762852142.79 58906746862.78 59028845166.74 59044679705.76 59178106163.73 59190426614.98 59308628179.3  59308628566.3  59314873579.7  59314873579.8  59370942190.79 59748865774.78 59805822339.78 59805822339.81 60138129582.99 60277639852.86 60468873383.76 60499277734.69 60634079619.10060634079619.76 60679622738.73 60679622738.76 61230833468.78 6165337146.79  6166287527.72  61874979822.75 61917199020.75 61919296171.99 62091965166.76 62131122447.76 62131122447.82 62625805991.77 62948418713.80 62989950816.81 62989950828.75 63174103918.76 6320660206.78  63235321891.97 63235321901.71 63341493050.80 64398247470.99 64556005486.76 64758730450.73 64758730450.76 6501784985.78  65104334021.84 65104452412.5  65129926126.80 65417393774.80 65673252078.79 65759081031.69 65805175866.75 66443298926.76 67258535356.76 67323469228.86 67434480419.86 67449453465.75 67471419575.85 831511534.76   8405736896.100 8405736896.99  8474926972.71  8733664836.71  8989589102.76  9079110254.77  97018265.80    9767205155.86  9802357102.80  00000400800=00A00E00I00J00K00L00M00N00O00P00Q00R00V00_00`00i01201301401501901=01F01J01N01W01X01\01`01d01h01n02302402=02F02K02L02M02V02W02`02a02b02c02h03103203;03?03C03L03M03N03R03V03W03`03e03n03o04004104:04>04G04H04I04J04K04O04S04T04]04o05005505>05?05@05E05N05R05V05_05c05d05e05j05o06006106506606:06C06P06]06b06f06j06k07007407507607;07D07H07L07U07^07_07h07n08208608?08@08A08E08F08G08K08T08X08\08`08a08j08k09409509>09G09H09Q09R09Y09`09m0::0:G0:N0:U0:b0:c0:h0:m0;10;50;60;70;@0;I0;J0;N0;R0;S0;T0;U0;Z0;_0;`0;a0;b0;k0<40<50<>0<?0<@0<A0<J0<S0<\0<e0<f0<j0<n0<o0=00=50=90==0=A0=J0=K0=T0=]0=^0=_0=c0=g0>00>90>B0>C0>D0>M0>N0>O0>X0>\0>]0>a0>e0>f0>o0?40?D0?H0?I0?J0?S0?\0?e0?f0?g0?k0?o0@80@A0@B0@C0@D0@M0@T0@c0A50A>0AG0AH0AI0AR0AV0AW0A[0A\0A]0Af0Ao0B30B80B90BB0BF0BJ0BS0BT0BU0BV0BW0B[0B_0Bh0C10C50C90C>0CG0CP0CY0Cb0Cc0D00D=0DF0DO0DX0DY0D^0Dg0Dk0Do0E<0E=0EB0EK0EL0EM0EN0EO0EX0Ea0Eb0Eo0F8S2LOS2LOS3SPRS2HBS2LOS2LOSSSSSSSSSS2HBS4CEIL2LOSS4CEIL2LOS4CEIL2LOSSSS2LOS2LOS4CEIL2LOS2HBS2HBS4CEIL2LOSS2HBS2HBS2LOS2LOS4SPOSS3SPRSS4CEIL2LOS4CEIL2LOS3SPRSSS4CEIL2LOSS4CEIL2LOSSSS3SPRS4CEIL2LOSS4CEIL2LOS2HBS2HBS4CEIL2LOSSS2LOS2LOSS4CEIL2LOS3SPRS4CEIL2LOSSSS4CEIL2LOS2HBS4CEIL2LOSSSSS2LOS2LOSS4CEIL2LOS4CEIL2LO4SPOS3AM3SS3SALS4CEIL2LOSSS3SPRS4CEIL2LOS2LOS2A0S4CEIL2LOS2HBSSS3SPRS3SPRSSS2HBSS2LOS4CEIL2LOS4SPOS2A03ASZS4SPOS2A03ASZS3SPRS2HBS2A0SS3SPRS2LOSSS3SPRS4CEIL2LOS2LOS2LOS4CEIL2LOS4CEIL2LOSS4CEIL2LOS2A01HS2LOS2LOS4CEIL2LOSSS2HBSSS2HBS4CEIL2LOS2LOS2LOS2LOSS4CEIL2LOSS4CEIL2LOSS4CEIL2LOS4CEIL2LOSS4CEIL2LOSS2A02K1S2A02K1S4SPOS2A03ASZS4SPOS2A03ASZS4SPOS2A03AM3S2A02K1S2A02K1S4SPOS2A03AM3SS3SPRS3SPRS2LOS2HBSSS4CEIL2LOS4CEIL2LOSS2LOS2LOSSSS3SPRS3SPRSSSS4CEIL2LOS4CEIL2LOSS4CEIL2LOSSSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSS2LOS2LOSSS3AALS2LOS2LOS2HBS4CEIL2LOSS4CEIL2LOS4CEIL2LOSSS2LOS2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSSS4CEIL2LOSSS4CEIL2LOS2HBSS2LOS2LOSS4CEIL2LOS3SPRS4SPOS3AM23AM31HS2LOSSS4CEIL2LOS4CEIL2LOS4CEIL2LOSSS2LOS2LOS4CEIL2LOS4CEIL2LOSSSS4NAME2K0S2A02K3S4SPOS3AM32LT1HS4SPOS3AM32K11H2K2S4CEIL2LOS4CEIL2LOSSS4CEIL2LOS2A0SS2LOSSS4CEIL2LOS4CEIL2LOS2HBS3SPRSS4CEIL2LOS2LOS2LOS4CEIL2LOSSSSS2LOS2LOS4CEIL2LOS4CEIL2LOS2LOS2LOS3SPRS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSS4SPOS2A03AM3S4SPOS2A03ASZS4CEIL2LOS4CEIL2LOS4CEIL2LOSS3SPRS4CEIL2LOS2HBS2A0S4CEIL2LO3AM3SS3ASZS4CEIL2LOFFSSS4CEIL2LOS4CEIL2LOSS4CEIL2LO3AM3S4CEIL2LO".
carve_frame 32%nat ST.
  step. step. step. step. step. step. step.
  step. step. step. step.                                      (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
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
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 NAME. lia. }   (* [comment removed for export] *)
  step. step. step. lstep.                                     (* [comment removed for export] *)
  zstep. step. if_lit.                                         (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  step. step. step. step. step. step. step. step. step.        (* [comment removed for export] *)
  release_frame FR1 ST (bv_unsigned sp + -128).
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
  apply (munch_weaken _ [(bv_unsigned sp - RMAP_STACK, bv_unsigned sp); (addr, addr + size)]%Z) in MU.
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
  lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -128) _, STK : stk bsegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp + -32) end.
  (* [comment removed for export] *)
  replace (ret_pc (Z_to_bv 64 448648)) with (Z_to_bv 64 448648 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  step. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by (clear -A0 ASZ SPOS; unfold AIMG_HI in *; lia). clear -K3 A0. lia. }
  step. step. step. step. step. step.
  lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -32) _, STK : stk bsegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  apply evtF_done. right. split; [reflexivity|].
  do 15 eexists. split. 2: reflexivity.
  unfold rmap_post, rmap_postD. destruct HF0 as [[FPLE _] [_ BW]].
  split; [exact FPLE|]. split; [exact AM3|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [exact ZNEW|]. split; [exact GR1|]. split; [exact GR2|]. split; [exact BW|].
  unfold rmap_cells. repeat (split; [assumption|]). assumption.
  Unshelve. all: apply ref_ro_addr_false; right; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC2.
