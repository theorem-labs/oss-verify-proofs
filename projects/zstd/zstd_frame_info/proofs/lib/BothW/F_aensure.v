(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import MM_syscalls.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import SysStepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg AProto ABase AKit AKit2 ARep ARepFrame RT_stubs F_apoison F_aalloc3 F_ammap.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
Local Ltac aload ST8 i AEXPR :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let RD := fresh "RD" in
    pose proof (u64arr_read bsegs mm A ws i (nth (Z.to_nat i) ws w0) (wa AEXPR) ST8
                  ltac:(apply nth_error_nth'; rewrite ?upd_length; lia) ltac:(lia) ltac:(f_equal; lia)) as RD;
    step; clear RD
  end.
Local Ltac astore ST8 i :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let SOK := fresh "SOK" in
    pose proof (u64arr_store_ok bsegs mm A ws i (wa (A + 8 * i)) ST8 ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
    step;
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) (le8 ?v)) _) =>
      let S2 := fresh "STATS" in
      pose proof (u64arr_write bsegs mm A ws i v ST8 ltac:(rewrite ?upd_length; lia)) as S2;
      replace (A + 8 * i)%Z with E in S2 by lia;
      clear ST8; store_done; try clear SOK; rename S2 into ST8
    end
  end.

Section CANSEC1. Context {rc : runConstT}.
Definition ensure_entry := 0x33ee0.
End CANSEC1.
Notation ENSURE_STACK := 448 (only parsing).    (* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Definition m3_cells (L : alayout) (m : amem) : Prop :=
     poison_cells m /\ rmap_cells m
  /\ rw_cells bsegs m 0xa08a0 [C1 (Z_to_bv 8 1)] /\ rw_cells bsegs m 0xa08a4 [C4 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] /\ rw_cells bsegs m ATSD [C8 (Z_to_bv 64 (al_ctx L))]
  /\ rw_cells bsegs m (al_ctx L + 152) [C8 (Z_to_bv 64 (al_t L))]
  /\ rw_cells bsegs m 0x9d9f8 [C8 (Z_to_bv 64 (al_space_beg L))]                      (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x9da00 [C4 (Z_to_bv 64 4294967295)]                            (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x9da08 [C8 (Z_to_bv 64 (al_space_beg L + K_SPACE_SIZE))]       (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x9da10 [C1 (Z_to_bv 8 0)].                                      (* [comment removed for export] *)

#[using="Type"] Lemma m3_cells_frame : forall L m m' W, m3_cells L m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => (AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) /\ (snd iv <= al_ctx L + 152 \/ al_ctx L + 160 <= fst iv)) W -> m3_cells L m'.
Proof.
  intros L m m' W (PC & RC & C1' & C2 & C3 & C4' & C5 & C6 & C7 & C8' & C9) MU WM HW.
  assert (D : forall A k, 0 <= k -> A + k <= 0x5f6000 -> 0x10000 <= A -> disjoint_from W A k).   (* [comment removed for export] *)
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

#[using="Type"] Lemma m3_cells_frame_rc : forall L m m' W, m3_cells L m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => (AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) /\ (snd iv <= al_ctx L + 152 \/ al_ctx L + 160 <= fst iv)) W -> rmap_cells m'.
Proof. intros L m m' W MC MU WM HW. exact (proj1 (proj2 (m3_cells_frame L m m' W MC MU WM HW))). Qed.

(* [comment removed for export] *)
Definition ensure_ret (L : alayout) (RNG : footprint) (sp : word) (st : astate) (c nf lo : Z) (sj : list word) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let r := get_cls st c in let FA := afreearr L c in let mfa := c_mapped_free_array r in
  fp_le RNG RNG' /\
  exists new sj',
     (   (4 * nf <= mfa /\ new = mfa /\ st2 = st /\ RNG' = RNG)
      \/ (mfa < 4 * nf /\ new = rup (4 * nf) K_FREEARR_MAP /\ st2 = put_cls c (cls_set_mapped_free_array new r) st
          /\ rw_cells bsegs m' (FA + mfa) [CB (Z.to_nat (new - mfa)) (repeat (Z_to_bv 8 0) (Z.to_nat (new - mfa)))]
          /\ fill_at m' (shad (FA + mfa)) (shlen (new - mfa)) 0xfa
          /\ rng RNG' (FA + mfa) (new - mfa) /\ rng RNG' (shad (FA + mfa)) (shlen (new - mfa)) /\ fp_bw RNG'))
  /\ 4 * nf <= new <= K_FREEARR_MAX /\ mfa <= new /\ new mod K_FREEARR_MAP = 0
  /\ munch [(bv_unsigned sp - ENSURE_STACK, bv_unsigned sp); (FA + mfa, FA + new); (shad (FA + mfa), shad (FA + mfa) + shlen (new - mfa));
            (al_t L + 2800, al_t L + 3168); (aregion_info L c + 24, aregion_info L c + 32)]%Z m m'
  /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
  /\ rw_cells bsegs m' (aregion_info L c + 16)
       [C8 (Z_to_bv 64 (c_num_freed r)); C8 (Z_to_bv 64 new); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0);
        C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)]
  /\ u64arr bsegs m' (al_t L + 2800) sj' /\ length sj' = 46%nat
  /\ azero m' (shad (FA + new)) (shlen (K_FREEARR_MAX - new))
  /\ m3_cells L m'.

#[using="Type"] Lemma rup18_facts : forall x, 0 <= x -> x <= rup x 262144 <= x + 262143 /\ rup x 262144 mod 262144 = 0 /\ (x mod 262144 = 0 -> rup x 262144 = x).
Proof. intros x Hx. unfold rup. Local Ltac2 Set LiaHints.tbl := fun () => "0010=20995551440.3000001S".
OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma ensure_spec : forall RNG {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c nf lo : Z) (sj : list word),
  let r := get_cls st c in let RI := aregion_info L c in let FA := afreearr L c in let mfa := c_mapped_free_array r in
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - ENSURE_STACK ->
  mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 RI -> a2 = Z_to_bv 64 (aregion L c) -> a3 = Z_to_bv 64 nf ->
  m3_cells L m ->
  rw_cells bsegs m (RI + 16)
     [C8 (Z_to_bv 64 (c_num_freed r)); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)] ->
  u64arr bsegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  (* [comment removed for export] *)
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 -> 0 <= nf -> 4 * nf <= K_FREEARR_MAX ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      ensure_ret L RNG sp st c nf lo sj m st2 RNG' m' ->
      implS bsegs RNG' (aembed ATOP (k st2 true)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (aembed ATOP (ensure_free_array st c nf k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ensure_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until sj. cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> MC REG STATS LSJ AZ SBE HC MFA MFAM NF NF4 SP1 SP2 SP3 CX0 CX1 T0 T1 TCX SCX TSP RIMG RSTK RCTX RT RRI CXI TIC KONT. band_lin.   (* [comment removed for export] *)
  box TCX. box SCX. box TSP.
  pose proof MC as MC0. destruct MC0 as (PC & RC & TI & TK & T88 & TSD & CT & ISB & IREL & ISE & IPRE).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, ensure_entry in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR.
  set (mfa := c_mapped_free_array (get_cls st c)) in *.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - ENSURE_STACK, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  iprefix.
  Local Ltac2 Set LiaHints.tbl := fun () => "04a0?1047820382.13  10600373102.10310649802198.16310822766052.16610830758748.16 10830758748.19 11647286254.10111777263255.10411797343393.16011797343393.16111799489569.16611805467289.10111805467289.10311805467289.10411805467289.17211805598740.19 11807744665.10 11807744665.16212334040174.10312428150072.16412429510126.10412429510126.1721279872003.10  14055389725.28 14251140644.13 14761575534.10314793086774.11214793086774.14614793086774.16114993016302.10315045184517.16015045184517.16115387613978.17116111536342.16016152533917.15816423910102.16016449464117.11216458268297.96 16961996613.26 170773230.104  17141182446.10117277026341.13 1733136316.3   17534156933.16117534156933.16217632079770.10517776320428.16517776320431.10217776320431.10317803025398.15817986879152.13 17986879152.23 1800609155.103 1800609155.104 1800609155.166 18276986478.10418611522902.16118770195838.16519617313304.22 19617313304.37 20416174892.17220431170854.16220567797462.16020734795990.16020794827301.23 20857051927.10320919340534.16 21418064110.10421533188226.10721533188226.17222207912957.9  22208176125.28 22226902198.16122233892466.17322264047035.8  22389541692.10122700267513.16722706556809.10 22837444294.26 22952216122.17222954650507.6  23253790359.10323868974523.10623868974523.17124344800857.16624487705898.1022452149659.168 24559830510.10424559830510.17224638473347.10424638473347.10524638473347.16725065190167.17 25065190167.18 25065190167.21 25071498650.19 25076071819.16425076071819.16525792348067.16426019439157.2  26229383790.10326578924325.11226586770331.1012658730222.104 26690313645.15826961506542.10427019834838.16127117329262.10327189741570.16027290117426.16127294894486.16127523246446.10327574660131.16627904909209.15927905056697.96 28132537239.10428417259964.10328767017635.16429313596044.23 29403793238.1613047548758.161 30603927662.10330832715758.10131007531734.16031378308326.94 31784914262.16132071826473.17132107039626.13632270060963.16432335205627.11 32335205627.26 32740259714.16133062543571.23 33298494999.10433399844006.16033405859426.17033680001082.10434430152252.10435013046373.28 35042221400.26 35520726249.7  36053106009.16636115622446.10336115622446.10436115622447.16637845668334.10437845668334.1723794754569.5   37952880771.3  38238797294.10438238797294.17238938709062.26 39617088189.50 40059657198.10440059657198.17240243014947.16440243747043.16440457739452.10340608002030.10140672532759.10340938375116.13 41168710592.23 41417988426.3  42013680038.19 4222606119.5   42238456215.10442488118638.10342805740039.16442995994990.10343059266230.92 4322745501.28  43551704186.23 43950383598.10143987951406.10343987951406.10443987951407.16643988483203.10143988483203.10343988483203.16544253452910.10344487020398.16644545694830.10345221239098.10445221239098.17245235952921.16645242657588.54 45246060169.55 45297343979.16145380827299.16445415010670.10345848756903.10145889153637.13645889153764.13746024503395.16746024503395.1694605342103.12  46468661564.10446801997731.3  47002471715.16447237230212.28 47805607814.3  48170605038.10148316456345.17248654615790.10348724676119.10349081171875.3  49125819609.16649476425441.17249476425454.16449481019365.28 49649769127.10449744878297.16650310179909.4  50885398489.12 50978328983.10151318623851.1605138071929.9   51705425809.96 51711223320.95 51721692860.15851866641414.15852105090727.10352436114006.16052567164907.17252575291859.16052575291859.16152622824343.1015305926510.103 5316791447.104 53180773481.7  53326475118.10153376910608.28 53767577772.16553767577775.10253767577775.10353877920417.16054243526019.10354243526019.10454243526019.16654388338902.16054532700782.10354969794426.13 55113301982.16455207105262.10455225214521.23 5522898774.161 55590199162.19 56170256219.11156170256219.14556170256219.1605622855209.111 563227834.103  57378835438.10457378835438.17257425246934.16057622410744.16557628700040.10 57745675194.1035787935796.28  59308628433.6  59308630630.6  59314873579.13 59565103882.19 59788593288.28 60080207907.16460471841134.10460471841134.17260571393319.17260858483367.10461529484705.19 61599171566.10461599171566.17261723695716.6  61957295940.3  62019383790.10162973951777.16163042061173.4  63235321900.10063235321900.10263235321901.16463255209115.16563305555623.10363713694743.10363776448791.10464997134979.10464997134979.10564997134979.16765809644505.16666989839702.1616725418733.5   67681843542.16168055296919.10368501319406.1047455691504.9   766265084.1    7773822379.28  8469793241.166 8583720762.101 8608697945.166 876831355.5    8806423751.9   8875530120.23  8879755827.6   9372136215.101 9956545262.104 00000800A00B00[00g01601?01S01T01U02G02H02I02J02K02[02a03K03T03U03^03n04804K04S04\04k05:05I05R05W05\05]05f05k06406906>06G06P06Y06]06a06f06k07307707;07?07@07F07L07M07N07O07X07a08808908:08;08<08E08N08R08f09J09S09T09U09e0:20:30:40:C0:G0;d0;h0<40<80<@0<M0<R0<W0<d0<e0<j0=30=C0=D0=E0=F0=W0=k0>E0>]0@>0@?0@Q0@U0@^0@n0A?0AH0AM0AV0A_0Ah0Al0Am0An0B70B80B<0B@0BP0BT0Bf0C30C<0CE0CN0CW0C`0Ca0Cj0Ck0Cl0D>0DM0D\0D`0Da0Dn0Do0E00E50E90EF0EJ0ES0E`0Ed0Eh0El0F50FE0FI0FQ0FZ0Fj0G?0G@0GI0GY0Gk0H=0HA0HJ0HZ0Ho0I00I10I20I70IK0IT0IU0I^0Ib0Ie0J00J90J=0JA0JE0JF0JG0JH0JQ0JR0J[0J`0Jd0K10K20K30K<0KN0KW0KX0Ki0L=0LB0LC0LR0LV0LW0Li0M60M70M@0MY0Mb0N60N>0NK0NL0NQ0NV0NW0Nd0Ne0O20OB0OK0OW0OX0OY0OZ0O[0O\0Oe0Of0Og0Oh0P<0PE0PU0P^0Pg0Q00Q40Q80Q<0QH0QI0QJ0QK0QT0Q]0Qb0RH0RQ0RV0R_0Rj0Ro0S40S90S:0S?0SH0SX0Sa0U>0UB0UG0UL0UP0U`0Uh0Ui0V=0VO0VX0Vh0WC0WD0WI0WR0Wb0Wc0Wg0X00X<0XD0XH0XL0XP0XU0XV0Xf0Y30Y40Y50Y60YC0YL0YP0YY0Yf0Yo0Z90Z:0ZO0Z\0Za0Zn0[30[70[D0[I0[V0[_S3CX12T1S4CEIL2LOSS4CEIL2LO3SP23FA33FA53HspS2HC3FA33FA5S3FA33FA53FA01YS4CEIL2LOS4CEIL2LO2HC3SP23RIESSS4CEIL2LO4SHF24SHF33Hsp3CX13MFA3SP23FA33FA53LSJ2T1SSSSS4CEIL2LO2HC3SP2S2HC1YS3LSJ3MFA3SP13FA23FA52K14SHF14SHF24SHF32T2S4CEIL2LOFS4CEIL2LOS3SP12KC3FA53FA0S3FA52P21HS2HC3MFA3SP13FA02Y0S2HC3SP2S4CEIL2LOS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS4CEIL2LOS3LSJS3LSJFS3LSJ3TICS3LSJS3LSJ3TICS3MFAS3MFAS3FA23SHTS4CEIL2LOS4CEIL2LOS2LOS2LOS3LSJS3LSJS2NF3NF4S2LOS2LOS2LOSS4CEILS4CEILSSSS4CEIL2LOS3LSJ3TICS4CEIL2LO4SHF24SHF33HspFFSSS3LSJ3TICS3LSJ3TICS2LOS4CEIL2LO2HC3SP23RIES2HC3MFA4MFAM3SP13SP33KE'3RU13RU22KCS4CEIL2LOSSS2HC3MFA3SP13SP2S3SP13FA03CX2SSS4CEIL2LO3CX11HS2HBS4CEIL2LO3LSJ2HC3MFA4MFAM3NF43SP13SP22T13KE'3RU13RU23RU32KC3FA23FA33FA52K14SHF24SHF32T23Hsp1HS2HxS2HC3SP13SHTS2HBS2HC3MFAS4CEIL2LO3CX1S3RIES3RIES4CEIL2LO3HspSS3LSJS4CEIL2LOS3SP12KC3FA53FA0SSSS4CEIL2LO3SP23FA3S4CEIL2LO2HC3SP23FA3S4CEIL2LO3SP22T13FA33FA01YS4CEIL2LO2HC3MFA3SP13SP2S4CEIL2LO3LSJ3MFA4MFAM3SP13CX13KE'3RU13RU23RU33FA23FA52K14SHF14SHF23CX23Hsp3NF43SP23FA33FA02T12T2FS4CEIL2LO4SHF13HspS2NFS4CEIL2LOS3MFA3KE'3RU12KCS3MFA3NF43KE'3RU1S4CEIL2LOS3LSJS4CEIL2LOS3LSJ3TICS4CEIL2LOS2T1SSS4CEIL2LOFS2LOS2LOS4CEIL2LO3LSJ2T1S2HBS4CEIL2LO4SHF13HspS3FA23FA43FA5S3LSJ3TICS3LSJ3TICS4CEIL2LOS4CEIL2LOS3LSJ3TICSS3LSJ3TICFSS4CEIL2LO4SHF13HspS4CEIL2LO3SHR1HS4CEIL2LO3SHT1HS2T1SS4CEIL2LO3CX1SSS3SPRS2HBS3MFA3SP13FA0S2SES3KE'3RU1S4CEIL2LO3HspS2LOS2LOS2LOS4CEIL2LOS3SP12KC3FA53FA0S2KES2NF3NF4S4CEIL2LOS3SP12KC3FA53FA0S4SHF14SHF32SE3SHT2T1FS4CEIL2LOS3SP12KC3FA53FA0S4CEIL2LO4SHF13HspS4CEIL2LO4SHF13HspS2HBS4CEIL2LOS4CEIL2LO3LSJ2T1S3SP23FA23FA33FA43FA5SSSS3KE'S4CEIL2LO2HC3SP23RIES4CEIL2LOFS4CEIL2LOS2LOS1YS3SP23FA31HS4CEIL2LOS2LOS2LOS2LOSSSS4CEIL2LOFS4CEIL2LOS3SPRS2HBS4CEIL2LO3HspFFS3LSJ3TICS4CEIL2LO4SHF13HspS4CEIL2LOSS3SP23FA23FA33FA5S2K23SP23FA23FA33FA5S3LSJSS3SP23FA33FA51HS2HBSS4CEIL2LO4SHF13HspS4CEIL2LO3CX1SS4CEIL2LOS4CEIL2LO3MFA3SP23FA33FA5S4CEIL2LOS4CEIL2LO2HC3SP23RIES2NF3NF4S4CEIL2LO3HspSS3LSJS3TICSS4CEIL2LO3HspSS3SP23FA23FA3S4CEIL2LO3LSJ2T1S3LSJ3TICS3KE'3RU12KCFSSSSS3LSJ3TICSSSS4CEIL2LO2HC3SP23RIES4CEIL2LOS4CEIL2LO3LSJ2T1S3MFA3KE'S4CEIL2LOS4CEIL2LOS2LOS2LOS2LOS4CEIL2LO2T1SSSS3LSJ3TICS4CEIL2LOS3CXIS4CEIL2LO3SP13SP23FA33FA53FA04SHF23HspS4CEIL2LOS3FA5S3LSJ3TICS3SP23FA31HS3HspS3HspS3HspFS3SPRS4CEIL2LOS3SP12KC3FA53FA0S3LSJ3TICS4CEIL2LO3LSJ2HC3MFA4MFAM3NF43SP13SP22T13KE'3RU13RU23RU32KC3FA23FA33FA52K14SHF24SHF32T23Hsp1HS2HxS3SPRS3FA2S2K2S3NF43RU13RU22KCS3FA22K1SS3SP13FA33FA02Y03CX2S4CEIL2LO4SHF13HspS4CEIL2LOS3SP12KC3FA53FA0S3NF43SP13KE'3FA04SHF24SHF3SS3FA2S4CEIL2LOS3SP12KC3FA53FA0SS2KCS4CEIL2LOS4CEIL2LO2T1S3RU12KCS2LOS2LOS2LOS3LSJSS4CEIL2LO3LSJ2T1S4CEIL2LO3CX1SSSS4CEIL2LO3HspS3LSJ3TICS2KES3LSJ3TICS4CEIL2LO3CX1S4CEIL2LOS4MFAM3RU2SS3SP13SP23FA33FA03CX2S4CEIL2LO3HspS3SPRS4CEIL2LO3HspS3KE'S2HxS3FA13FA23FA5S3FA1S4CEIL2LO3CX1S4CEIL2LO".
carve_frame 48%nat ST.
  step. step. step. step. step. step.                          (* [comment removed for export] *)
  rewrite RIE in REG |- *. rewrite FAE in AZ.
  step.                                                        (* [comment removed for export] *)
  zstep. step.                                                 (* [comment removed for export] *)
  step. if_cases KE; zify_cond KE.                             (* [comment removed for export] *)
  { (* [comment removed for export] *)
    assert (KE' : 4 * nf <= mfa) by (rewrite Z.shiftl_mul_pow2, Z.mod_small in KE by (clear -NF NF4; lia); clear -KE; lia). clear KE.
    step. step. step. step. step. step. step. step.            (* [comment removed for export] *)
    lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -48) _, STK : stk bsegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
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
      { rewrite shad_div, shlen_div. unfold ASHOFF. clear -SP1 SP2 HC MFA. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
      clear -SHR CEIL LO. split; [lia| exact I].
    - eapply m3_cells_frame; [exact MC | exact MU | exact WM |].
      apply Forall_cons; [cbn [fst snd]; clear -CEIL LO CX1; unfold AIMG_HI, AIMG_LO; lia | apply Forall_nil]. }
  (* [comment removed for export] *)
  assert (KE' : mfa < 4 * nf) by (rewrite Z.shiftl_mul_pow2, Z.mod_small in KE by (clear -NF NF4; lia); clear -KE; lia). clear KE.
  pose proof (rup18_facts (4 * nf) ltac:(clear -NF; lia)) as (RU1 & RU2 & RU3).
  set (new := rup (4 * nf) 262144) in *.
  zstep. zstep. zstep. zstep. zstep.                           (* [comment removed for export] *)
  setreg 8 (Z_to_bv 64 new) ltac:(rewrite Z.shiftl_mul_pow2, land_align2p18 by (clear -NF NF4; lia); f_equal;
                                   subst new; unfold rup; clear -NF NF4; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  zstep. zstep. step. if_cases KC; zify_cond KC. { exfalso. clear -KC RU1 RU2 NF4. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }   (* [comment removed for export] *)
  lstep.                                                       (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
  unfold aregion, K_REGION. change (2^32) with 4294967296.
  setreg 9 (Z_to_bv 64 (al_space_beg L + c * 4294967296 + 3758096384 + mfa)) ltac:(f_equal; clear; lia).
  step. if_lit.                                                (* [comment removed for export] *)
  step. zstep. step. step. step. step.                         (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  apply evtF_done. unfold ensure_free_array.
  replace (nf * 4 <=? c_mapped_free_array (get_cls st c)) with false by (symmetry; apply Z.leb_gt; fold mfa; clear -KE'; lia).
  replace (rup (nf * 4) K_FREEARR_MAP) with new by (subst new; unfold K_FREEARR_MAP; f_equal; clear; lia).
  replace (K_FREEARR_MAX <? new) with false by (symmetry; apply Z.ltb_ge; unfold K_FREEARR_MAX; clear -KC; lia).
  cbv iota. unfold ev. rewrite aembed_vis. cbn [aev_tree]. unfold PROT_RW, F_FIXED.
  unfold region_beg, K_REGION, K_FREEARR_OFF. change (2^32) with 4294967296. rewrite SBE. fold mfa.
  set (FAM := al_space_beg L + c * 4294967296 + 3758096384 + mfa) in *.
  assert (FAM8 : FAM mod 4096 = 0 /\ 0x10007fff8000 <= FAM /\ FAM + (new - mfa) <= al_space_beg L + 137438953472 /\ (new - mfa) mod 4096 = 0 /\ 0 < new - mfa).
  { subst FAM. clear -SP1 SP3 HC MFA MFAM KE' RU1 RU2 KC NF. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
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
  { (* [comment removed for export] *)
    intros a RNG' ms' NE P1 P2. unfold fixed_answer_ok, is_err, TWO64.
    replace (2 ^ 64 - 4096 <? a) with false by (symmetry; apply Z.ltb_ge; clear -P2 FA5; atop_facts; lia).
    replace (a =? FAM) with false by (symmetry; apply Z.eqb_neq; exact NE). cbn [negb orb]. rewrite aembed_aundef_. apply implF_ret_unr. }
  (* [comment removed for export] *)
  intros RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' RP.
  destruct RP as (FPLE & _ & MU2 & WM2 & MI2 & ST2 & ZNEW & GR1 & GR2 & BW & RC2). unname_sp.
  (* [comment removed for export] *)
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RCTX.
  apply (rng_fp_le _ _ _ _ FPLE) in RT. apply (rng_fp_le _ _ _ _ FPLE) in RRI.
  (* [comment removed for export] *)
  xport FR MU2 WM2 ltac:(clear -SPR CEIL LO FA2 FA3 SP2; lia).
  xport REG MU2 WM2 ltac:(clear -SPR CEIL LO FA2 FA3 SP2 HC; lia).
  xport STATS MU2 WM2 ltac:(rewrite LSJ; ub TSP; clear -SPR CEIL LO FA0 FA2 FA3 SP2 T0 T1 Y; lia).
  clear ST. rename ST2 into ST.
  assert (AZ2 : azero m2 (shad FAM) (shlen (536870912 - mfa))).
  { eapply azero_frame; [eapply azero_frame; [exact AZ | exact MU | exact WM |] | exact MU2 | exact WM2 |];
      intros _; cbn [disjoint_from]; subst FAM; rewrite ?shad_div, ?shlen_div; unfold ASHOFF;
      clear -SPR CEIL LO SP1 SP2 HC MFA KC RU1 KE'; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  assert (MUF : munch [(bv_unsigned sp - ENSURE_STACK, bv_unsigned sp); (FAM, FAM + (new - mfa)); (shad FAM, shad FAM + shlen (new - mfa));
                       (al_t L + 2800, al_t L + 3168); (al_space_beg L + 137438953472 + c * 128 + 24, al_space_beg L + 137438953472 + c * 128 + 32)]%Z m m2).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; clear; intros x Hx; lia. }
  clear MU MU2. pose proof (wmono_trans _ _ _ _ WM WM2) as WMF. clear WM WM2.
  assert (WOK : Forall (fun iv => (AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) /\ (snd iv <= al_ctx L + 152 \/ al_ctx L + 160 <= fst iv))
           [(bv_unsigned sp - ENSURE_STACK, bv_unsigned sp); (FAM, FAM + (new - mfa)); (shad FAM, shad FAM + shlen (new - mfa));
            (al_t L + 2800, al_t L + 3168); (al_space_beg L + 137438953472 + c * 128 + 24, al_space_beg L + 137438953472 + c * 128 + 32)]%Z).
  { ub TCX. ub SCX. unfold AIMG_HI, AIMG_LO.
    do 5 (apply Forall_cons; [cbn [fst snd]; clear -CEIL LO CX0 CX1 T0 T1 TIC SP1 SP2 HC MFA FA0 FA2 FA3 KC Y Y0;
                              with_band CX0 ltac:(rewrite ?shad_div, ?shlen_div; unfold ASHOFF; split; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia) |]). apply Forall_nil. }   (* [comment removed for export] *)
  pose proof (m3_cells_frame L m m2 _ MC MUF WMF WOK) as MC2.
  clear TI TK T88 TSD CT ISB IREL ISE IPRE.
  pose proof MC2 as MC2'. destruct MC2' as (PC2 & _ & TI & TK & T88 & TSD & CT & ISB & IREL & ISE & IPRE). unfold ATP88, ATSD in T88, TSD.
  (* [comment removed for export] *)
  replace (ret_pc (Z_to_bv 64 212864)) with (Z_to_bv 64 212864 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  iprefix.
  step. if_cases K1; zify_cond K1. { exfalso. clear -K1 FA2 FA3 SP2. rewrite ?unsigned_lit in K1 by lia. lia. }   (* [comment removed for export] *)
  step. step. if_cases K2; zify_cond K2. { exfalso. clear -K2. lia. }                                                (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  pose proof (azero_cb m2 _ _ (shlen (new - mfa)) AZ2 ltac:(rewrite !shlen_div; clear -MFA KC KE' RU1; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia)) as SHCB.
  clear AZ2.
  assert (SHF : 0x2008fff7000 <= shad FAM /\ shad FAM + shlen (new - mfa) <= 0x10007fff8000 /\ 0 < shlen (new - mfa)).
  { rewrite shad_div, shlen_div. unfold ASHOFF. clear -FA2 FA3 FA4 FA5 SP2. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  destruct SHF as (SHF1 & SHF2 & SHF3).
  step. with_band CX0 ltac:(with_band T0 ltac:(call_sp (poison_shadow_spec RNG' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FAM (new - mfa) 250 lo))).   (* [comment removed for export] *)
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => first [assumption | unfold ablk; right; clear -FA2 FA3 SP2; lia]   (* [comment removed for export] *)
       | |- stk _ _ _ _ => first [ match goal with HH__ : stk _ _ _ _ |- _ => eexact HH__ end | eassumption ]
       | |- mem_inv _ _ => assumption
       | |- poison_cells _ => exact PC2
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ (shad _) _ => exact SHCB
       | |- rng _ (shad _) _ => exact GR2
       | |- rng _ _ _ => solve_rng
       end.
  all: try (atop_facts; clear -FA1 FA2 FA3 FA4 FA5 SP2 CEIL LO KC RU1 KE' MFA; rewrite ?shlen_div; first [lia | OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]).
  (* [comment removed for export] *)
  step. with_band T0 ltac:(call_sp (thread_stats_spec RNG' (al_ctx L) (al_t L) lo)).   (* [comment removed for export] *)
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => first [ match goal with HH__ : stk _ _ _ _ |- _ => eexact HH__ end | eassumption ]
       | |- mem_inv _ _ => assumption
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- rw_cells _ _ _ _ => assumption
       | |- rng _ _ _ => solve_rng
       end.
  all: try (unfold AIMG_HI; clear -CEIL LO CX0 CX1 T0 T1 CXI TIC; lia).
  all: match goal with |- ?G => idtac "REMT" G end.
  aload STATS 10 (al_t L + 2800 + 80). aload STATS 9 (al_t L + 2800 + 72).
  zstep. zstep.                                                (* [comment removed for export] *)
  snapshot [(al_t L + 2800, al_t L + 3168)]%Z MUs WMs.
  box CT. box ZNEW. box REG.
  lazymatch goal with P : rw_cells bsegs _ (shad FAM) _ |- _ => rename P into SHPO end. box SHPO.   (* [comment removed for export] *)
  astore STATS 9. astore STATS 10.
  carry SHPO MUs WMs ltac:(with_band T0 ltac:(lia)).
  carry REG MUs WMs ltac:(ub TSP; clear -HC T0 T1 SP1 SP2 Y; lia).
  carry CT MUs WMs ltac:(ub TCX; clear -HC CX0 CX1 T0 T1 Y; lia).
  carry ZNEW MUs WMs ltac:(ub TSP; clear -HC T0 T1 SP1 SP2 FA0 FA2 FA3 FA5 Y; lia).
  clear MUs WMs.
  snapshot [(al_space_beg L + 137438953472 + c * 128 + 24, al_space_beg L + 137438953472 + c * 128 + 32)]%Z MUr WMr.
  box CT. box ZNEW. box STATS.
  step. step.                                                  (* [comment removed for export] *)
  carry CT MUr WMr ltac:(ub SCX; clear -HC CX0 CX1 SP1 SP2 Y; lia).
  carry ZNEW MUr WMr ltac:(clear -HC SP1 SP2 FA0 FA2 FA3 FA5; lia).
  carry STATS MUr WMr ltac:(rewrite ?upd_length, LSJ; ub TSP; clear -HC T0 T1 SP1 SP2 Y; lia).
  clear MUr WMr.
  step. step.                                                  (* [comment removed for export] *)
  step. step. step. step. step. step. step.                    (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -48) _, STK : stk bsegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  apply evtF_done.
  unfold fixed_answer_ok, is_err, TWO64. rewrite Z.eqb_refl.
  replace (2 ^ 64 - 4096 <? FAM) with false by (symmetry; apply Z.ltb_ge; clear -FA3 FA5 SP2; lia). cbn [negb orb].
  eapply KONT. unfold ensure_ret, K_FREEARR_MAX, K_FREEARR_MAP. cbv zeta. fold mfa. split; [exact FPLE|].
  lazymatch goal with |- context [u64arr bsegs _ _ ?ws] => idtac | H : u64arr bsegs _ (al_t L + 2800) ?ws |- _ => exists new, ws end.
  rewrite FAE, RIE. fold FAM.
  split. { right. split; [exact KE'|]. split; [subst new; f_equal; clear; lia|]. split; [reflexivity|].
           split; [exact ZNEW|]. split; [assumption|]. split; [exact GR1|]. split; [exact GR2| exact BW]. }
  split; [clear -RU1 KC; lia|]. split; [clear -RU1 KE'; lia|]. split; [exact RU2|].
  split. { eapply munch_weaken; [| exact MUF]. unfold sub_fp, FAM. cbn [outside]. clear. intros x Hx. lia. }
  split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [assumption|]. split; [assumption|]. split; [rewrite ?upd_length; exact LSJ|].
  split.
  { pose proof (azero_split m _ _ (shlen (new - mfa)) AZ ltac:(rewrite !shlen_div; clear -MFA KC KE' RU1; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia)) as AZT.
    replace (shad FAM + shlen (new - mfa)) with (shad (FAM + (new - mfa))) in AZT by (apply shad_add_shlen; clear -FA1; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    replace (shlen (536870912 - mfa) - shlen (new - mfa)) with (shlen (536870912 - new)) in AZT by (rewrite !shlen_div; clear -FA4 MFAM RU2 MFA; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    replace (al_space_beg L + c * 4294967296 + 3758096384 + new) with (FAM + (new - mfa)) by (unfold FAM; clear; lia).
    eapply azero_frame; [exact AZT | exact MUF | exact WMF |]. intros Hp. cbn [disjoint_from].
    pose proof (shad_add_shlen FAM (new - mfa) ltac:(clear -FA1; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia)) as SE.
    assert (SHT : shad (FAM + (new - mfa)) + shlen (536870912 - new) <= 0x10007fff8000).
    { rewrite shad_div, shlen_div. unfold ASHOFF, FAM. clear -SP2 KC RU1 MFA HC KE'. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
    clear -SE SHT SHF1 SHF2 SHF3 CEIL LO FA2 FA3 FA5 T0 SP1 SP2 HC. with_band T0 ltac:(repeat split; lia). }   (* [comment removed for export] *)
  eapply m3_cells_frame; [exact MC | eassumption | eassumption | exact WOK].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC2.
