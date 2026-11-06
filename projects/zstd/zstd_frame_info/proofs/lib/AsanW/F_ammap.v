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
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg AProto ABase AKit AKit2 RT_stubs.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition rmap_entry := 0x6d858.
End CANSEC1.
(* [comment removed for export] *)
Notation RMAP_STACK := 400 (only parsing).   (* [comment removed for export] *)
Notation RMAPD_STACK := 368 (only parsing).  (* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Definition rmap_cells (m : amem) : Prop :=
     rw_cells asegs m 0x98e18 [C8 (Z_to_bv 64 0x130920)]
  /\ rw_cells asegs m 0x130920 [C8 (Z_to_bv 64 4096)]
  /\ rw_cells asegs m 0x98e28 [C8 (Z_to_bv 64 0x1329a8); C8 (Z_to_bv 64 0x9e678); C8 (Z_to_bv 64 0xa0e78);
                               C8 (Z_to_bv 64 0xa1b68); C8 (Z_to_bv 64 0xa1b70); C8 (Z_to_bv 64 0xa1b60)]
  /\ rw_cells asegs m 0x132aac [C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m 0x132a38 [C8 (Z_to_bv 64 0)].

#[using="Type"] Lemma rmap_cells_frame : forall m m' W, rmap_cells m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => AIMG_HI <= fst iv) W -> rmap_cells m'.
Proof.
  intros m m' W (R1 & R2 & R3 & R4 & R5) MU WM HW. unfold AIMG_HI in HW.
  assert (D : forall A k, 0 <= k -> A + k <= 0x5f6000 -> disjoint_from W A k).
  { clear -HW. intros A k Hk HA. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. Local Ltac2 Set LiaHints.tbl := fun () => "0080>1017271774.13 21644381342.1330296331679.1133666907028.1335768103838.1338826358686.1343418671902.1368060973103.1300000100200900:00;00<00=00>SSS2HA2H1SSSSS".
split; [lia| apply IH; assumption]. }
  unfold rmap_cells. repeat lazymatch goal with |- _ /\ _ => split end;
    (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn; apply D; lia]).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Definition rmap_postD (D : Z) (RNG : footprint) (sp : word) (addr size lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG'
  /\ addr + size <= ATOP
  /\ munch [(bv_unsigned sp - D, bv_unsigned sp); (addr, addr + size)]%Z m m' /\ wmono asegs m m'
  /\ mem_inv asegs m'
  /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' addr [CB (Z.to_nat size) (repeat (Z_to_bv 8 0) (Z.to_nat size))]
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
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RMAP_STACK ->
  mem_inv asegs m ->
  a1 = Z_to_bv 64 addr -> a2 = Z_to_bv 64 size -> 0x10000 <= bv_unsigned a3 < 2^47 ->
  addr mod 4096 = 0 -> size mod 4096 = 0 -> 0 < size -> AIMG_HI <= addr -> addr + size < 2^63 ->
  rmap_cells m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  (forall a RNG' ms', a <> addr -> 0 < a -> a + size <= ATOP -> implS asegs RNG' (K a) (epostF Q) ms') ->
  (forall RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      rmap_post RNG sp addr size lo m RNG' m' ->
      implS asegs RNG' (K addr) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap addr size 3 50) (adec_mmap ATOP size 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rmap_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> -> NAME AAL SAL SPOS A0 ASZ RC RIMG RSTK UNR KONT. unfold AIMG_HI in A0.
  pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & GOT & DPM & MLIM).
  unfold rmap_entry in *. word_range sp SPR. word_range a3 A3R.
  pose proof (munch_refl [(bv_unsigned sp - RMAP_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  eapply (implF_ebind _ _ _ _ _ _ _
            (fun a RNG' ms' => (a <> addr /\ 0 < a /\ a + size <= ATOP) \/ a = addr /\ exists m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
               rmap_post RNG sp addr size lo m RNG' m' /\
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom asegs))).
  2: { intros a RNG' ms' [(NE & P1 & P2)|[-> PO]]; [apply UNR; [exact NE | exact P1 | exact P2]|].
       destruct PO as (m' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & PO & ->).
       eapply KONT. exact PO. }
  (* [comment removed for export] *)
  iprefix.
  (* [comment removed for export] *)
  Local Ltac2 Set LiaHints.tbl := fun () => "04g0?10439767981.76 10439767981.77 10667180602.80 10835893820.80 11303324790.81 1162083374.77  1164180522.100 11805467289.72 11805467289.73 11805467289.74 11805467289.75 11805467289.76 11805467289.77 11805467289.78 11805467289.79 11805467289.80 11833462140.99 12017784537.99 12429510126.75 12866317849.78 12974414830.76 13084834179.78 13084834179.81 1340665966.76  13725786656.82 13725786670.79 14689973870.76 14761575534.74 15062336688.76 15600526930.73 15600526930.76 15685060272.73 15779085422.76 15788225262.80 16622434386.73 16622434386.76 16781328285.76 16844590268.77 17221588796.72 17544628206.78 17776320429.72 17778417576.98 17976286208.2  1809810926.80  18689773242.77 19006120615.75 19139298862.99 19376804346.99 19491992743.75 19879235054.80 20289765031.77 21931701891.80 21931701891.83 21934774638.80 22080489625.78 22163107130.78 22232942.78    22249017454.77 22439364775.76 22711797486.75 22872305980.80 22927418606.79 23012552174.78 23230285244.74 23619845358.78 23715658734.80 23882872046.75 23909860377.78 24018494190.79 24080369177.78 24179267756.77 24179267758.80 2435347822.78  24487705898.73 24630998586.78 25029166211.10125029166211.78 25071629079.99 25117511228.78 25435258127.73 25435258127.99 25566553219.75 25566553219.99 25627738222.75 25876173099.99 25878270254.77 26000888601.77 26115614154.99 26278908583.76 26431752469.6  26868428163.76 26868428163.98 27066288442.77 27514742894.76 27679091076.67 27797263342.77 28885198780.78 29349361518.79 29514832494.74 29515017603.77 29515017603.78 30196181434.76 30231011258.78 30518562691.10030518562691.76 30603927662.74 31143001276.76 31193132057.78 31319825774.78 31420974624.72 31539821806.75 31929422315.78 31940628442.70 32377744366.75 32631783278.78 32651489978.76 32905389884.77 33148315118.76 33342412455.78 33680001082.72 33941110538.84 34288016811.98 34290115814.66 34570277878.99 35082589626.78 3520940321.81  3520940335.78  3551070382.99  35677373209.76 35900719086.80 36107562391.89 36115622435.97 36115622445.74 36367760551.78 36654913774.72 36981022702.78 37044431129.77 37153923388.75 37609348206.77 37845668334.75 38214450030.78 38399784046.78 38725888878.72 38806986883.72 38806986883.98 38916199868.78 39219183342.78 39238442350.78 39939624357.86 40091925667.97 40091925676.75 40259044249.79 40269695990.99 40286936842.86 40613224310.98 40987550979.99 41564619544.85 42309226734.78 4240063612.85  42501437472.10042501437472.99 42503534630.75 42505299482.70 42509314849.83 42511603879.86 42511604512.86 42511604641.85 42817538363.86 42831019478.73 42831019478.76 42882700782.77 43059266230.64 43183609788.76 43231650947.80 43231650947.83 43466089753.76 43985854248.98 43987951407.74 4413803118.76  44158664835.75 44158664835.98 44187290284.86 44621604505.77 4497338734.78  45221239098.75 46232973498.76 46234544622.78 46356275438.72 46556098215.78 47230136046.79 47373904281.79 48355031171.77 48355031171.80 48538816594.73 48538816594.76 48673721966.76 49255081006.99 49562070382.78 49710714478.77 49750950894.75 49903997356.86 50215255347.76 50703419246.78 50862133932.77 50862133934.80 50882889347.79 50882889347.82 51041686382.76 51254863854.77 51495837550.75 51585900270.78 51612993474.6  51678667180.75 51680764331.99 5180980284.75  51933874855.78 53324805799.79 53540834542.79 53618414247.80 53676604142.75 53767577772.73 53769674920.98 53853382510.76 53904676268.86 54148288295.99 54300395630.76 54367113454.80 54618151079.74 5496517358.76  55104759171.74 55104759171.99 55467843644.79 55681940633.77 5575378989.76  5575378991.79  55837769369.80 56084093934.77 563227834.74   56426686290.73 56426686290.76 56712086766.78 56759370246.7  56993697826.86 5745572519.80  57756175257.80 58618836718.78 58655119491.10058655119491.78 58762852128.82 58762852142.79 59044679705.76 59178106163.73 59308628179.3  59308628566.3  59314873579.7  59314873579.8  59805822339.78 59805822339.81 60274535852.86 60468873383.76 60499277734.69 60634079619.10060634079619.76 61170136174.77 61230833468.78 61423245358.99 61439603310.74 61519228526.76 6165337146.79  6166287527.72  61778293102.76 61917199020.75 61919296171.99 62131122447.76 62131122447.82 62343778002.73 62343778002.76 62625805991.77 62948418713.80 6297249326.99  62989950816.81 62989950828.75 63002572398.80 63235321891.97 63235321901.71 63341493050.80 6501784985.78  65104334021.84 65104452412.5  65666169454.77 65759081031.69 65805175866.75 66094744694.99 66554270958.80 66571591084.86 67258535356.76 67434480419.86 67449453465.75 67471419575.85 6783195886.80  68062769646.74 68501319406.72 698988910.76   7373603310.77  8405736896.100 8405736896.99  8474926972.71  8733664836.71  97018265.80    9767205155.86  9956545262.72  00000400800=00A00B00F00J00K00L00M00N00O00P00Q00R00S00W00X00a00b00k00l00m01601:01>01G01P01T01]01f01j02302<02E02N02O02S02W02`02d02h02n03703<03=03F03K03L03U03V03W03X03a03b03g04004904:04C04G04P04Y04]04f04o05805905B05C05G05K05T05U05Z05[05\05]05a05b05c05d05e05n06206606706I06J06O06P06Q06V06_06c06l07007907B07C07D07I07N07O07P07Y07]07^07g07k08408A08N08W08`08e08i09209309809909=09>09?09D09H09L09U09V09_09e09i09m09n0:70:@0:A0:E0:N0:W0:`0:i0;20;30;40;80;A0;J0;N0;R0;V0;W0;X0;Y0;Z0;[0;\0;e0;f0;m0<40<A0<N0<[0<b0<i0=60=70=<0=A0=J0=N0=R0=S0=T0=U0=Y0=]0=f0=g0=h0=l0=m0>60>;0>@0>I0>R0>S0>\0>]0>^0>_0>h0?10?:0?C0?L0?U0?^0?b0?c0?l0@00@40@50@60@?0@H0@Q0@Z0@_0@c0@g0@k0@l0@m0A60A70A@0AD0AH0AQ0AU0AV0A_0Ah0Ai0B20B30B40B80B90B=0BA0BB0BK0BP0BY0Bb0Bk0C;0C?0C@0CA0CJ0CK0CL0CP0CT0CU0CV0C_0Cf0D50DG0DH0DI0DM0DN0DR0DS0DT0D]0Da0Dj0E30E<0EA0EB0EK0EO0ES0ET0EU0E^0Eg0Eh0Ei0F20F60F:0FC0FG0FK0FP0FQ0F^0Fk0G40G50G:0G;0GD0GH0GL0GY0GZ0G_0Gh0H10H:0HC0HL0HM0HN0HO0HP0HQ0H^0HgS2LOS2LOS3SPRS2HBSS2LOS2LOSSSSSSSSSS2HBSS4CEIL2LOSS4CEIL2LOSSS4CEIL2LOS2LOS2LOS4CEIL2LOS4CEIL2LOS2HBS4CEIL2LOS4CEIL2LOS2HBS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSS2HBS2HBS4CEIL2LOS2LOS2LOS4SPOSS4CEIL2LOS3SPRSS4CEIL2LOS3SPRSS4CEIL2LOSSSS4CEIL2LOSS3SPRS4CEIL2LOS4CEIL2LOSS4CEIL2LOS2HBS4CEIL2LOS4CEIL2LOS2HBS4CEIL2LOS4CEIL2LOS4CEIL2LOSS4CEIL2LOSS2LOS2LOS4CEIL2LOSS3SPRSSSS2HBSSSSS4CEIL2LOS2LOS2LOSS4CEIL2LO4SPOS3AM3SS3SALSSS3SPRS4CEIL2LOS2LOS4CEIL2LOS2HBS4CEIL2LOS4CEIL2LOSSS3SPRS3SPRSSS4CEIL2LOS2HBSS4CEIL2LOS2LOS4CEIL2LOS4SPOS2A03ASZS4SPOS2A03ASZS4CEIL2LOS4CEIL2LOS3SPRS2HBS4CEIL2LOSS3SPRSS2LOSSS3SPRS2LOS2LOS4CEIL2LOSS4CEIL2LOS2A01HS2LOS2LOSS4CEIL2LOS4CEIL2LOSS2HBS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSSS2HBS4CEIL2LOS4CEIL2LOS2LOS2LOS2LOSSSSSSS4CEIL2LOSS2A02K1S2A02K1S4SPOS2A03ASZS4SPOS2A03ASZS4SPOS2A03AM3S2A02K1S2A02K1S4SPOS2A03AM3SS3SPRS3SPRS4CEIL2LOS2LOS2HBSSSS2LOS2LOS4CEIL2LOSSS2A0SS4CEIL2LOS3SPRS3SPRS4CEIL2LOS4CEIL2LOSS4CEIL2LOSSSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS2A0SS4CEIL2LOS2LOS2LOSSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS3AALS2LOS2LOS2HBSSS4CEIL2LOSS4CEIL2LOS2LOS2LOS4CEIL2LOS2A0SS4CEIL2LOS4CEIL2LOSS4CEIL2LOSSS2HBSS2LOS2LOSS4CEIL2LOS3SPRS4CEIL2LOS4CEIL2LOS4CEIL2LOS4SPOS3AM23AM31HS2LOSSS4CEIL2LOSSS2LOS2LOSSS4NAME2K0S2A02K3S4SPOS3AM32LT1HS4SPOS3AM32K11H2K2SSS2A0SS2LOSSS4CEIL2LOS2HBS4CEIL2LOS4CEIL2LOS4CEIL2LOS3SPRSS4CEIL2LOS2LOS2LOSSS4CEIL2LOS4CEIL2LOSSS4CEIL2LOS2LOS2LOS4CEIL2LOS2LOS2LOS3SPRSS4SPOS2A03AM3S4SPOS2A03ASZS4CEIL2LOSS3SPRSS4CEIL2LOS2A0S2HBS4CEIL2LO3AM3SS3ASZS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOFFSSSS4CEIL2LO3AM3S4CEIL2LO".
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
  replace (ret_pc (Z_to_bv 64 415436)) with (Z_to_bv 64 415436 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
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
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -128) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp + -32) end.
  (* [comment removed for export] *)
  replace (ret_pc (Z_to_bv 64 448644)) with (Z_to_bv 64 448644 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  step. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by (clear -A0 ASZ SPOS; unfold AIMG_HI in *; lia). clear -K3 A0. lia. }
  step. step. step. step. step. step.
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -32) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
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
