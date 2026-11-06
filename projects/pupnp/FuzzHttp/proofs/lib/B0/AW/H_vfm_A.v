(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require H_scanner_get_token.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import AWUb HttpRepA AWKit AWAuto AWAuto2 FakeKit HObjK HObjF H_scanner_get_token.
Import ListNotations.
Open Scope Z_scope.

Definition vfmatch_entryA : Z := 0x86acc.
Notation VA_HEAD := 0x86c84%Z.
Notation VA_DISP := 0x86ca8%Z.
Notation VA_CONT := 0x86c84%Z.
Notation VA_ERR := 0x877e0%Z.
Notation VA_EPI := 0x877fc%Z.
Notation VMASK := 4294977024%Z.
Notation VJT_A := 0x211ec%Z.

Definition vjt356_A : list byte := map (Z_to_bv 8)
  [40; 91; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 40; 91; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 216; 93; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 220; 95; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 20; 97; 6; 0; 152; 90; 6; 0; 116; 94; 6; 0; 112; 97; 6; 0; 152; 90; 6; 0; 144; 97; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 176; 98; 6; 0; 112; 93; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 208; 95; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 128; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 216; 96; 6; 0; 152; 90; 6; 0; 208; 98; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 152; 90; 6; 0; 148; 93; 6; 0; 112; 93; 6; 0]%Z.
Lemma vjt_bytes_A : forall m, mem_inv asegs m -> bytes_at asegs m VJT_A vjt356_A.
Proof.
  intros m MI. pose proof (ro_cells_image asegs m VJT_A vjt356_A MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO.
  destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Definition vjt_off_A (c2 : Z) : Z :=
  if c2 =? 99 then 418480 else if c2 =? 115 then 418512 else if c2 =? 120 then 417136 else if c2 =? 83 then 418160
  else if c2 =? 76 then 417756 else if c2 =? 105 then 417744 else if c2 =? 119 then 417172 else if c2 =? 82 then 417396 else 0.
Definition vjt_char (c2 : Z) : bool := ((c2 =? 99) || (c2 =? 115) || (c2 =? 120) || (c2 =? 83) || (c2 =? 76) || (c2 =? 105) || (c2 =? 119) || (c2 =? 82))%bool.
Lemma vjt_read_A : forall m c2, mem_inv asegs m -> vjt_char c2 = true ->
  ov_read_bytes asegs m (wa (VJT_A + 4 * (c2 - 32))) 4 = Some (le4 (Z_to_bv 64 (vjt_off_A c2))).
Proof.
  intros m c2 MI Hc. pose proof (vjt_bytes_A m MI) as B.
  assert (CASES : c2 = 99 \/ c2 = 115 \/ c2 = 120 \/ c2 = 83 \/ c2 = 76 \/ c2 = 105 \/ c2 = 119 \/ c2 = 82).
  { unfold vjt_char in Hc. repeat (apply orb_prop in Hc; destruct Hc as [Hc|Hc]); try (apply Z.eqb_eq in Hc; lia). }
  destruct CASES as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]];
    (rewrite (bytes_at_read asegs m VJT_A vjt356_A _ 4 B) by (cbn; lia)); f_equal; apply P0.H_scanner_get_token.bytes_eqb_eq; vm_compute; reflexivity.
Qed.

Lemma land_255_smallA : forall c, (0 <= c < 256)%Z -> Z.land c 255 = c.
Proof. intros c Hc. change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Section W.
Context {HC : HasCeiling}.
Hypothesis IC : icpt_contracts.
Variable FI : fs_if.
Hypothesis STACK_MALLOC_1 : stack_malloc_stmt FI 1.
Local Notation FSIV W := ((FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: W)%Z.

Definition vf_okA (q lo S MB A len cap cur0 : Z) (bs : list byte) (st : fsstate FI) (Wx : list ivl) : Prop :=
  alloc_ceiling <= lo /\ lo <= q - 304 - 8192 /\ q mod 16 = 0 /\ q <= 2^47
  /\ 0x609000 <= MB /\ MB + 32 <= S /\ S + 24 <= alloc_ceiling /\ S mod 8 = 0 /\ MB mod 8 = 0
  /\ lb (fs_live FI st) MB (S + 24 - MB)
  /\ 0 <= A /\ A + Z.of_nat (length bs) <= alloc_ceiling /\ Z.of_nat (length bs) >= len /\ len <= cap /\ A + cap + 1 < 2^63
  /\ 0 <= cur0 <= len
  /\ (A + Z.of_nat (length bs) <= MB \/ S + 24 <= A)
  /\ (A + Z.of_nat (length bs) <= FSB FI \/ FSB FI + A0_FS_SIZE <= A)
  /\ (A + Z.of_nat (length bs) <= 0x7fff7000 \/ 0x10007fff8000 <= A)
  /\ Forall (fun iv : ivl => fst iv <= snd iv /\ (lb (fs_live FI st) (fst iv) (snd iv - fst iv) \/ (0x5e7508 <= fst iv /\ snd iv <= 0x5e7510))) Wx
  /\ disjoint_from Wx A (Z.of_nat (length bs)) /\ disjoint_from Wx MB (S + 24 - MB)
  /\ (0 < len -> 0 < A).
Ltac vokA V := destruct V as (CLO & LO & AL16 & QHI & MBLO & MBS & SHI & SAL & MBAL & PLB & A0 & AHI & LBS & CAP & ACAP & CUR0 & TXP & TFS & TBAND & WXL & WXT & WXP & ANZ).

Section DEFS.
  Variables (q lo S MB A len cap cur0 : Z) (bs : list byte) (st : fsstate FI) (Wx : list ivl) (FMT flen : Z).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (m0 : mem).

  Definition vF := fs_F FI st 1.  Definition vFL := fs_FL FI st 1.  Definition vst1 := fs_next FI st 1.  Definition vSF := sh vF.
  Notation F := vF. Notation FL := vFL. Notation st1 := vst1. Notation SF := vSF.
  Notation WV := ((S + 8, S + 16) :: Wx)%Z.
  Notation W0 := ((lo, q) :: FSIV WV)%Z.

  Definition vWL (q' : Z) : list ivl := ((lo, q' + 184) :: WV)%Z.

  Definition vWP (q' : Z) (WD : list ivl) : list ivl := ((lo, q' + 184) :: (S + 8, S + 16) :: WD)%Z.

  Definition vSHC : Z := Z.shiftr (S + 8) 3 + 2147450880.
  Definition vSHE : Z := Z.shiftr (S + 16) 3 + 2147450880.

  Definition vrest (q' : Z) (m : mem) : Prop :=
    (q' = q + -288 \/ q' = q + -288 - 16)
    /\ stk asegs m (q' + 184) (q + -104)
    /\ rw_cells asegs m (q + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m F [C8 (wz 0x41b58ab3); C8 (wz 0x17079); C8 (wz 0x86acc); C8 (wz q')]
    /\ (exists e j, rw_cells asegs m (F + 32) [C8 e; CB 80 j])
    /\ rw_cells asegs m (F + 120) [C8 (wz FL)]
    /\ rw_cells asegs m SF [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
                            C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
                            C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243);
                            C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m FL [C1 (Z_to_bv 8 1)]
    /\ munch W0 m0 m /\ wmono asegs m0 m
    /\ fkeep FI WV st m0 m /\ RFAKE FI st1 m
    /\ fs_live FI st1 = fs_newff FI st 1 :: fs_live FI st.

  Definition vscr (q' G cs : Z) (m : mem) : Prop :=
    exists w0 w16 w32,
      rw_cells asegs m q' [C8 w0; C8 (wz (Z.land (S + 16) 7 + 3)); C8 w16; C8 (wz (F + 32)); C8 w32; C8 (wz cur0); C8 (wz VMASK); C8 (wz F); C8 (wz F);
                           C8 (wz SF); C8 (wz vSHE); C8 (wz (S + 16)); C8 (wz cs); C8 (wz (F + 64)); C8 (wz G); C8 (wz (S + 8)); C8 (wz F)].
  Definition vtok (q' : Z) (m : mem) : Prop :=
    exists j136 tyA tbA tlA j160 tyB tbB tlB,
      rw_cells asegs m (q' + 136) [CB 4 j136; C4 tyA; C8 tbA; C8 tlA; CB 4 j160; C4 tyB; C8 tbB; C8 tlB].

  Definition vinv (q' cur G cs : Z) (m : mem) : Prop :=
    stk asegs m lo q' /\ vscr q' G cs m /\ vtok q' m
    /\ rw_cells asegs m S [C8 (wz MB); C8 (wz cur); C4 (wz 0)]
    /\ rw_cells asegs m MB (mbuf_cells A len cap)
    /\ bytes_at asegs m A bs
    /\ mem_inv asegs m /\ asan_env asegs m
    /\ shw m S 24 /\ shw m MB 32 /\ (0 < len -> shw m A len) /\ shw m SEPTAB_A 20 /\ shw m FMT flen
    /\ shz m (sh lo) (sh q)
    /\ cur0 <= cur <= len
    /\ (q + -304 <= q' <= q + -288 /\ q' mod 16 = 0)
    /\ vrest q' m.

  Definition headstA (q' fp c : Z) (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 : word) (m : mem) : machine_state :=
    MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') (wz 4) (wz c) x12 x13 x14 x15 x16 x17
            x18 (wz S) (wz 4) (wz 1) (wz 2147450880) (wz vSHC) (wz fp) (wz (fp + 1)) x26 x27 x28 x29 x30 x31)
       F_ (wz VA_DISP) fc None m (seg_rom asegs).
  Definition contstA (q' r fp' : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x25 x26 x27 x28 x29 x30 x31 : word) (m : mem) : machine_state :=
    MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') (wz r) x11 x12 x13 x14 x15 x16 x17
            x18 (wz S) (wz 4) (wz 1) (wz 2147450880) (wz vSHC) (wz fp') x25 x26 x27 x28 x29 x30 x31)
       F_ (wz VA_CONT) fc None m (seg_rom asegs).
  Definition errstA (q' r : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) (m : mem) : machine_state :=
    MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') (wz r) x11 x12 x13 x14 x15 x16 x17
            x18 x19 x20 x21 x22 (wz vSHC) x24 x25 x26 x27 x28 x29 x30 x31)
       F_ (wz VA_ERR) fc None m (seg_rom asegs).
  Definition epistA (q' r : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (m : mem) : machine_state :=
    MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') (wz r) x11 x12 x13 x14 x15 x16 x17
            x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F_ (wz VA_EPI) fc None m (seg_rom asegs).
End DEFS.

Section VF.
  Variables (q lo S MB A len cap cur0 : Z) (bs : list byte) (st : fsstate FI) (Wx : list ivl) (FMT flen : Z).
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (m0 : mem).
  Hypothesis VOK : vf_okA q lo S MB A len cap cur0 bs st Wx.
  Hypothesis RF0 : RFAKE FI st m0.
  Hypothesis FCO : fs_call_ok FI st tp 1.
  Hypothesis FE0 : FSENV FI m0.

  Notation F := (vF st). Notation FL := (vFL st). Notation st1 := (vst1 st). Notation SF := (vSF st).
  Notation WV := ((S + 8, S + 16) :: Wx)%Z.
  Notation W0 := ((lo, q) :: FSIV WV)%Z.
  Notation SHC := (vSHC S). Notation SHE := (vSHE S).
  Notation vrest := (vrest q lo S st Wx ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0).
  Notation vscr := (vscr S cur0 st). Notation vtok := vtok.
  Notation vinv := (vinv q lo S MB A len cap cur0 bs st Wx FMT flen ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0).
  Notation headstA := (headstA q S gp tp F_ fc). Notation contstA := (contstA q S gp tp F_ fc). Notation errstA := (errstA q S gp tp F_ fc). Notation epistA := (epistA q gp tp F_ fc).

  #[using="m0 RF0"] Lemma lb_in_fs : forall a n, lb (fs_live FI st) a n -> FSB FI + 36864 <= a /\ a + n <= FSB FI + A0_FS_SIZE.
  Proof.
    intros a n (g & Hg & G1 & G2). pose proof (live_num FI st m0 RF0) as LN. rewrite Forall_forall in LN.
    destruct (LN g Hg) as (L1 & L2 & _). lia.
  Qed.
  #[using="Type"] Lemma sub_app_iv_fs : forall a b, FSB FI <= a -> a <= b -> b <= FSB FI + A0_FS_SIZE -> app_iv (a, b).
  Proof.
    intros a b H1 H2 H3. pose proof (fsb_ok FI) as (B1 & B2 & B3 & B4 & B5). unfold app_iv, SH_HI. cbn [fst snd]. lia.
  Qed.
  #[using="HC FI q lo S MB A len cap cur0 bs st m0 VOK RF0"] Lemma Wx_app : app_ivs Wx.
  Proof.
    vokA VOK. unfold app_ivs. eapply Forall_impl; [| exact WXL]. intros [a b] [LE [LB|ER]]; cbn [fst snd] in *.
    - destruct (lb_in_fs _ _ LB) as [H1 H2]. apply sub_app_iv_fs; lia.
    - unfold app_iv. cbn [fst snd]. left. lia.
  Qed.
  #[using="HC FI q lo MB A len cap cur0 bs st m0 VOK RF0"] Lemma WV_app : app_ivs WV.
  Proof.
    vokA VOK. constructor; [| exact Wx_app]. destruct (lb_in_fs _ _ PLB) as [H1 H2]. apply sub_app_iv_fs; lia.
  Qed.
  #[using="q lo MB A len cap cur0 bs st m0 VOK RF0"] Lemma WV_fsout : forall a, sh (FSB FI) <= a < sh (FSB FI) + A0_FS_SHSIZE -> outside WV a.
  Proof.
    intros a Ha. apply (app_ivs_outside WV a WV_app).
    pose proof (fsb_ok FI) as (B1 & B2 & B3 & B4 & B5). pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    unfold shband, SH_LO, SH_HI. unfold sh, SHADOW_OFF in Ha. clear - Ha B1 B2 ACR. Z.div_mod_to_equations. lia.
  Qed.
  #[using="MB A len cap cur0 bs st m0 VOK RF0"] Lemma W0_fsw : Forall (fsw_iv FI) W0.
  Proof.
    vokA VOK. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    apply fsw_cons_app; [apply app_iv_stack; lia|]. apply fsw_FSIV. exact WV_app.
  Qed.
  #[using="HC FI q lo MB A len cap cur0 bs st Wx VOK"] Lemma S_al : S mod 8 = 0.  Proof. vokA VOK. exact SAL. Qed.
  #[using="HC FI q lo S A len cap cur0 bs st Wx VOK"] Lemma MB_al : MB mod 8 = 0.  Proof. vokA VOK. exact MBAL. Qed.

  #[using="STACK_MALLOC_1 VOK RF0 FCO FE0"] Lemma prologue0V : forall (fp0 G : Z) t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (Q : machine_state -> Prop),
    stk asegs m0 lo q ->
    rw_cells asegs m0 S [C8 (wz MB); C8 (wz cur0); C4 (wz 0)] -> rw_cells asegs m0 MB (mbuf_cells A len cap) -> bytes_at asegs m0 A bs ->
    mem_inv asegs m0 -> asan_env asegs m0 ->
    shw m0 S 24 -> shw m0 MB 32 -> (0 < len -> shw m0 A len) -> shw m0 SEPTAB_A 20 -> shw m0 FMT flen ->
    shz m0 (sh lo) (sh q) ->
    0x10000 <= FMT -> FMT + flen <= 0x609000 ->
    (forall q' m x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x25 x26 x27 x28 x29 x30 x31, vinv q' cur0 G 1 m ->
       munch ((lo, q) :: FSIV []) m0 m -> wmono asegs m0 m -> fkeep FI [] st m0 m ->
       evt asegs Q (contstA q' 4 fp0 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x25 x26 x27 x28 x29 x30 x31 m)) ->
    evt asegs Q
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz S) (wz fp0) (wz G) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz vfmatch_entryA) fc None m0 (seg_rom asegs)).
  Proof.
    intros fp0 G t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Q ST SC MBC BUF MI AG SHS SHMB SHA SHSEP SHFMT SHZ FMT0 FMTHI K.
    pose proof VOK as VOK'. vokA VOK'. unfold vfmatch_entryA.
    hide SC. hide MBC. hide BUF. hide SHS. hide SHMB. hide SHA. hide SHSEP. hide SHFMT. hide SHZ. hide TXP. hide TFS. hide TBAND. hide ANZ.
    assert (PLS : lb (fs_live FI st) S 24) by (apply (Contracts.lb_sub _ _ _ _ _ PLB); lia). hide PLS.
    assert (PLM : lb (fs_live FI st) MB 32) by (apply (Contracts.lb_sub _ _ _ _ _ PLB); lia). hide PLM.
    clear WXL WXT WXP PLB.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof AG as AE. apply asan_env_globals in AG. ag_split AG.
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & _ & FSB4 & FSB5).
    assert (ESHB : sh (FSB FI) = FSB FI / 8 + 2147450880) by reflexivity.
    assert (ESF : SF = F / 8 + 2147450880) by reflexivity.
    destruct (new_frame_facts FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & FLO & FHI & FAL & FLLO & FLHI & APART).
    cbn [FB_of SB_of] in FHI. clear APART.
    assert (SFB : 8 * (SF - 2147450880) = F) by (rewrite ESF; clear - FAL; Z.div_mod_to_equations; lia).
    assert (SHB8 : 8 * (sh (FSB FI) - 2147450880) = FSB FI) by (rewrite ESHB; clear - FSB4; Z.div_mod_to_equations; lia).
    hide FAL. hide FSB4. hide ESF. hide ESHB. hide MBAL.
    pose proof (new_frame_fk FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
    pose proof (munch_refl W0 m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    pose proof (munch_refl ((lo, q) :: FSIV [])%Z m0) as MUF.
    pose proof (munch_refl [(lo, q)]%Z m0) as MU0. pose proof (wmono_refl asegs m0) as WM0.
    pose proof (fkeep_refl FI [] st m0) as FK. assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI st)) by (intros g Hg; exact Hg).
    pose proof RF0 as RF.
    carve_frame 288%nat ST.
    step. do 14 (step; fix_lit_store).
    step.
    step.
    rewrite (unsigned_lit (q + -288)) by lia. rewrite land_align32 by lia.
    remember (q + -288 - (q + -288) mod 32)%Z as q' eqn:Eq0.
    assert (Hq : q' = q + -288 \/ q' = q + -288 - 16) by (subst q'; apply align32_cases; clear - AL16; Z.div_mod_to_equations; lia).
    hide AL16.
    clear Eq0.

    lazymatch goal with FRx : rw_cells asegs ?mm (q + -288) (?c0 :: ?c1 :: ?rest) |- _ =>
      destruct (align_frame_gen mm lo (q + -288) q' [c0; c1] rest 184%nat ST ltac:(lia) FRx eq_refl ltac:(lia) Hq) as (STq & (jq & QC) & GAP & FRhi);
      clear FRx end.
    clear ST. rename STq into ST. assert (QB : q + -304 <= q' <= q + -288) by lia. hide Hq. change (Z.of_nat 184) with 184 in GAP, FRhi. replace (q + -288 + 184) with (q + -104) in GAP, FRhi by lia.
    step.
    sstep.
    step.
    step. step. step. step.
    step. step.
    step.
    step.   lit_branch.
    step.
    step.

    env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
    call (STACK_MALLOC_1 st lo q' 96 F SF FL 128 88%nat 16%nat).
    all: side (try (first [ assumption | reflexivity | (unfold A0_RT_STACK in *; lia) ])).

    match goal with A : asan_env asegs _ |- _ => try clear AE; rename A into AE end.
    match goal with R : RFAKE FI (fs_next FI st 1) _ |- _ => rename R into RF end.
    match goal with E : fs_live FI _ = _ :: _ |- _ => rename E into LIVE1 end. fold st1 in LIVE1, RF.
    match goal with K0 : fkeep FI [] st _ _ |- _ => rename K0 into FKc end.
    match goal with P : rw_cells asegs _ F _ |- _ => rename P into FRF end.
    match goal with P : rw_cells asegs _ SF _ |- _ => rename P into SHF; shadow_cells_lit SHF end.
    match goal with P : rw_cells asegs _ FL _ |- _ => rename P into FLG end.
    fs_after_call FI FK FKc LSUB LIVE1 [(lo, q); (F, F + 128); (SF, SF + 16)]%Z.
    pose proof (lb_new _ _ _ LIVE1) as LVF. pose proof (ls_new _ _ _ LIVE1) as LVS. pose proof (lf_new _ _ _ LIVE1) as LVL.
    unfold ff_size, ff_shsize in LVF, LVS. rewrite FCLS in LVF, LVS. cbn [FB_of SB_of] in LVF, LVS.
    change (ff_addr (fs_newff FI st 1)) with F in LVF, LVS. change (ff_flag (fs_newff FI st 1)) with FL in LVL. change (sh F) with SF in LVS.
    step.
    step.   if_cases K0; zify_cond K0. 2:{ exfalso. lia. } clear K0.
    sstep.
    do 8 step.
    step; fix_lit_store. step; fix_lit_store. step; fix_lit_store.
    step. step.
    replace (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 F)) 3 + 2147450880)) with (Z_to_bv 64 SF)
      by (f_equal; rewrite unsigned_lit by lia; rewrite shiftr3_div; unhide ESF; rewrite ESF; reflexivity).

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(SF, SF + 16)]%Z mm) as MUs; pose proof (wmono_refl asegs mm) as WMs end.
    hide_mem_except SHF. unhide MUs. unhide WMs.
    do 4 sstep.
    zstep.
    do 4 sstep.
    zstep.
    do 3 sstep.
    unhide_transport MUs WMs. clear MUs WMs.
    sstep.
    sstep.
    zstep.
    sstep. sstep.
    step. ubr_by ltac:(clear - KU SAL; lia).
    zstep. sstep. zstep. zstep.

    env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
    match goal with P : stk asegs _ lo q' |- _ => rename P into ST end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(lo, q)]%Z mm) as MU0; pose proof (wmono_refl asegs mm) as WM0 end.
    unhide PLS. unhide PLM.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (shw_fkeep0 FI st m0 mm S 24 SHS FK RF0 PLS) as SHS3;
      pose proof (rw_cells_fkeep FI [] st m0 mm S _ SC FK WM ltac:(solve_in_live) I) as SC3 end.
    cstep.
    cstep.
    step. zstep. sstep. zstep. sstep.
    step. sstep.
    zstep. zstep. zstep. zstep.
    zstep. sstep. zstep. zstep. zstep. sstep.
    zstep. sstep. zstep. sstep.
    zstep. zstep. sstep. step.

    env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
    unhide TXP. unhide TFS. unhide TBAND. unhide Hq. unhide MBC. unhide BUF. unhide SHA.
    pose proof VOK as VOK'. destruct VOK' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WXT & _).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (shw_fkeep0 FI st m0 mm S 24 SHS FK RF0 PLS) as SHSn;
      pose proof (shw_fkeep0 FI st m0 mm MB 32 SHMB FK RF0 PLM) as SHMBn;
      assert (SHAn : 0 < len -> shw mm A len)
        by (intros HL; apply (shw_frame_fs FI W0 m0 mm A len (SHA HL) MU W0_fsw); clear - TFS LBS; lia);
      pose proof (shw_frame_fs FI W0 m0 mm SEPTAB_A 20 SHSEP MU W0_fsw ltac:(left; unfold SEPTAB_A; lia)) as SHSEPn;
      pose proof (shw_frame_fs FI W0 m0 mm FMT flen SHFMT MU W0_fsw ltac:(left; lia)) as SHFMTn;
      pose proof (shz_stack_fs FI W0 m0 mm lo _ _ SHZ CLO (stack_lo_ok lo) (sh_hi_ok q QHI) MU W0_fsw) as SHZn;
      assert (MBCn : rw_cells asegs mm MB (mbuf_cells A len cap))
        by (unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in *; apply (rw_cells_fkeep FI [] st m0 mm MB _ MBC FK WM); [solve_in_live| exact I]);
      assert (BUFn : bytes_at asegs mm A bs)
        by (apply (bytes_at_transport asegs W0 m0 mm A bs BUF MU); cbn [disjoint_from];
            split; [lia|]; split; [clear - TFS; lia|]; split; [clear - TBAND SHB8 FSB1 FSB2 ACR; lia|]; split; [clear - TXP MBS; lia| exact WXT])
    end.
    assert (FKV : fkeep FI WV st m0 _) by (eapply (fkeep_weaken FI [] WV st st); [exact FK| intros xo _; exact I| intros g Hg; exact Hg]).

    recell QC 0%nat. recell QC 2%nat. recell QC 4%nat. split_chunk QC 17%nat SCR TOK.
    splitcb TOK 0%nat [4; 4; 8; 8; 4; 4; 8; 8]%nat. recell TOK 1%nat. recell TOK 2%nat. recell TOK 3%nat. recell TOK 5%nat. recell TOK 6%nat. recell TOK 7%nat.
    split_chunk FRF 4%nat FH FT. split_chunk FT 1%nat FT1 FT2. splitcb FT1 0%nat [8; 80]%nat. recell FT1 0%nat.
    replace (F + 32 + 88) with (F + 120) in FT2 by lia.
    name_junk SCR. name_junk TOK. name_junk FT1.
    apply K; [| exact MUF| exact WM| exact FK]. unfold vinv, vrest, vscr, vtok, vSHC, vSHE.
    split; [exact ST|]. split; [do 3 eexists; exact SCR|]. split; [do 8 eexists; exact TOK|].
    split; [exact SC3|]. split; [exact MBCn|]. split; [exact BUFn|]. split; [exact MI0|]. split; [exact AE|].
    split; [exact SHSn|]. split; [exact SHMBn|]. split; [exact SHAn|]. split; [exact SHSEPn|]. split; [exact SHFMTn|]. split; [exact SHZn|].
    split; [lia|]. split; [unhide AL16; clear - Hq AL16; split; [lia|]; Z.div_mod_to_equations; lia|].
    split; [exact Hq|]. split; [exact GAP|]. split; [exact FRhi|]. split; [exact FH|]. split; [do 2 eexists; exact FT1|]. split; [exact FT2|].
    split; [exact SHF|]. split; [exact FLG|]. split; [exact MU|]. split; [exact WM|]. split; [exact FKV|]. split; [exact RF|]. exact LIVE1.
  Qed.

  #[using="Type"] Lemma inside_In : forall (W : list ivl) iv, In iv W -> inside W (fst iv) (snd iv - fst iv).
  Proof.
    induction W as [|[a b] W IH]; intros iv HI; [destruct HI|]. cbn [inside]. destruct HI as [<- | HI]; [left; cbn [fst snd]; lia| right; exact (IH iv HI)].
  Qed.
  #[using="Type"] Lemma inside_cons : forall (W : list ivl) c a n, inside W a n -> inside (c :: W) a n.
  Proof. intros W [x y] a n H. cbn [inside]. right. exact H. Qed.
  #[using="FI q lo S MB A len cap cur0 bs st m0 VOK RF0"] Lemma Wx_below : forall a n, alloc_ceiling <= a -> 0 <= n -> disjoint_from Wx a n.
  Proof.
    intros a n Ha Hn. vokA VOK. pose proof (fsb_ok FI) as (B1 & B2 & _). clear - WXL Ha Hn B2 RF0.
    induction Wx as [|[x y] W IH]; cbn [disjoint_from]; [exact I|].
    inversion WXL as [|? ? [LE [LB|ER]] WXL']; subst; cbn [fst snd] in *.
    - destruct (lb_in_fs _ _ LB) as [H1 H2]. split; [right; lia| exact (IH WXL')].
    - pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR. split; [right; lia| exact (IH WXL')].
  Qed.
  #[using="q lo S MB A len cap cur0 bs m0 VOK RF0"] Lemma Wx_apart_new : forall a n,
    (F <= a /\ a + n <= F + 128) \/ (SF <= a /\ a + n <= SF + 16) \/ (a = FL /\ n = 1) -> disjoint_from Wx a n.
  Proof.
    intros a n HP. vokA VOK.
    destruct (new_frame_facts FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & FLO & FHI & FAL & FLLO & FLHI & APART).
    cbn [FB_of SB_of] in FHI, APART.
    assert (SHF1 : sh (FSB FI) <= SF /\ SF + 16 <= sh (FSB FI) + A0_FS_SHSIZE).
    { pose proof (fsb_ok FI) as (B1 & B2 & B3 & B4 & B5). unfold vSF, sh, SHADOW_OFF. clear - FLO FHI B4. Z.div_mod_to_equations. lia. }
    assert (LOW : 0x609000 <= F /\ 0x609000 <= SF /\ 0x609000 <= FL).
    { pose proof (fsb_ok FI) as (B1 & B2 & B3 & B4 & B5). unfold vSF, sh, SHADOW_OFF in *. clear - FLO FLLO SHF1 B1. Z.div_mod_to_equations. lia. }
    clear - WXL HP APART FLLO FLHI SHF1 RF0 LOW.
    induction Wx as [|[x y] W IH]; cbn [disjoint_from]; [exact I|].
    inversion WXL as [|? ? [LE [LB|ER]] WXL']; subst; cbn [fst snd] in *; (split; [| exact (IH WXL')]).
    - pose proof (lb_apart_frame _ _ _ F 128 _ _ LB APART) as P1.
      pose proof (lb_apart_shadow FI st m0 _ _ SF 16 RF0 LB ltac:(lia) ltac:(lia)) as P2.
      pose proof (lb_apart_flag FI st m0 _ _ FL RF0 LB FLLO FLHI) as P3.
      destruct HP as [HP|[HP|HP]]; lia.
    - right. destruct HP as [HP|[HP|HP]]; lia.
  Qed.
  #[using="Type"] Lemma Wx_fk : forall W', Forall (fk_ok FI (W' :: Wx) st) Wx.
  Proof.
    intros W'. apply Forall_forall. intros iv HI. left. apply inside_cons. exact (inside_In Wx iv HI).
  Qed.
  Notation WL := (vWL lo S Wx).
  Notation WP := (vWP lo S).

  #[using="MB A len cap cur0 bs VOK RF0"] Lemma vrest_step : forall q' m m', vrest q' m -> munch (WL q') m m' -> wmono asegs m m' -> vrest q' m'.
  Proof.
    intros q' m m' (Hq & GAP & FRhi & FH & (e & j & FT1) & FT2 & SHF & FLG & MU & WM & FK & RF & LIVE1) MUL WML.
    pose proof VOK as VOK'. vokA VOK'. clear TXP TFS TBAND WXT WXP.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & _ & FSB4 & _).
    destruct (new_frame_facts FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & FLO & FHI & FAL & FLLO & FLHI & APART).
    cbn [FB_of SB_of] in FHI, APART.
    assert (SHF1 : sh (FSB FI) <= SF /\ SF + 16 <= sh (FSB FI) + A0_FS_SHSIZE /\ SF + 16 <= lo /\ 0 <= SF /\ sh (FSB FI) + A0_FS_SHSIZE <= lo).
    { unfold vSF, sh, SHADOW_OFF. clear - FLO FHI FSB1 FSB2 FSB4 ACR CLO. Z.div_mod_to_equations. lia. }
    assert (QB : q + -304 <= q' <= q + -288) by (clear - Hq; lia). hide Hq.
    assert (PC8 : lb (fs_live FI st) (S + 8) 8) by (apply (Contracts.lb_sub _ _ _ _ _ PLB); lia).
    pose proof (lb_apart_frame _ _ _ F 128 _ _ PC8 APART) as P1.
    pose proof (lb_apart_shadow FI st m0 _ _ SF 16 RF0 PC8 ltac:(lia) ltac:(lia)) as P2.
    pose proof (lb_apart_flag FI st m0 _ _ FL RF0 PC8 FLLO FLHI) as P3.
    assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI st1)) by (intros g Hg; rewrite LIVE1; right; exact Hg).
    assert (DJS : forall a n, q' + 184 <= a -> 0 <= n -> disjoint_from (WL q') a n).
    { intros a n Ha Hn. unfold vWL. cbn [disjoint_from]. split; [right; lia|]. split; [right; lia|]. apply Wx_below; lia. }
    assert (DJF : forall a n, (F <= a /\ a + n <= F + 128) \/ (SF <= a /\ a + n <= SF + 16) \/ (a = FL /\ n = 1) -> disjoint_from (WL q') a n).
    { intros a n HP. unfold vWL. cbn [disjoint_from]. split; [left; clear - HP FHI FSB2 CLO SHF1 FLHI; lia|]. split; [clear - HP P1 P2 P3; lia|]. apply Wx_apart_new; exact HP. }
    unfold vrest. unhide Hq.
    split; [exact Hq|].
    split; [eapply stk_transport_disjoint; [exact GAP| exact MUL| exact WML| apply DJS; lia]|].
    split; [eapply rw_cells_transport; [exact FRhi| exact MUL| exact WML| apply DJS; [lia| simpl_sizes; lia]]|].
    split; [eapply rw_cells_transport; [exact FH| exact MUL| exact WML| apply DJF; left; simpl_sizes; lia]|].
    split; [exists e, j; eapply rw_cells_transport; [exact FT1| exact MUL| exact WML| apply DJF; left; simpl_sizes; lia]|].
    split; [eapply rw_cells_transport; [exact FT2| exact MUL| exact WML| apply DJF; left; simpl_sizes; lia]|].
    split; [eapply rw_cells_transport; [exact SHF| exact MUL| exact WML| apply DJF; right; left; simpl_sizes; lia]|].
    split; [eapply rw_cells_transport; [exact FLG| exact MUL| exact WML| apply DJF; right; right; simpl_sizes; lia]|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUL]. unfold vWL. intros xo Ho. cbn [outside] in *. destruct Ho as (H1 & _ & _ & H4). split; [lia| exact H4]. }
    split; [eapply wmono_trans; [exact WM| exact WML]|].
    split. { eapply fkeep_trans; [exact FK|]. eapply (fkeep_of_munch FI WV (WL q') st st1 m m m' RF LSUB MUL).
             unfold vWL. apply Forall_cons; [right; left; cbn [fst snd]; lia|]. apply Forall_cons; [left; cbn [inside fst snd]; left; lia|]. apply Wx_fk. }
    split; [| exact LIVE1].
    eapply (rfake_frame FI st1 m m' (WL q') RF MUL WML). unfold vWL.
    apply Forall_cons; [left; cbn [fst snd]; lia|].
    apply Forall_cons; [right; left; cbn [fst snd]; apply (lb_mono (fs_live FI st)); [apply (Contracts.lb_sub _ _ _ _ _ PC8); lia| exact LSUB]|].
    eapply Forall_impl; [| exact WXL]. intros iv [LE [LB|ER]]; [right; left; exact (lb_mono _ _ _ _ LB LSUB)|].
    left. clear - ER FSB1 SHF1. unfold sh, SHADOW_OFF in *. split; left; Z.div_mod_to_equations; lia.
  Qed.

  #[using="HC FI q MB A len cap cur0 bs st m0 VOK RF0"] Lemma WL_app : forall q', app_ivs (WL q').
  Proof.
    intros q'. pose proof VOK as VOK'. vokA VOK'. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    unfold vWL. constructor; [apply app_iv_stack; lia| exact WV_app].
  Qed.
  #[using="HC FI q MB A len cap cur0 bs st m0 VOK RF0"] Lemma WL_env : forall q', env_safe (WL q').
  Proof.
    intros q'. pose proof VOK as VOK'. vokA VOK'. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (FSB1 & _).
    unfold env_safe, vWL. constructor; [left; cbn [fst snd]; lia|]. constructor; [left; cbn [fst snd]; lia|].
    eapply Forall_impl; [| exact WXL]. intros iv [LE [LB|ER]]; [left; destruct (lb_in_fs _ _ LB) as [H1 H2]; lia|].
    do 6 right. left. exact ER.
  Qed.

  #[using="VOK RF0"] Lemma vinv_step : forall q' cur G cs cur' G' cs' m m',
    vinv q' cur G cs m -> munch (WL q') m m' -> wmono asegs m m' ->
    stk asegs m' lo q' -> vscr q' G' cs' m' -> vtok q' m' ->
    rw_cells asegs m' S [C8 (wz MB); C8 (wz cur'); C4 (wz 0)] ->
    rw_cells asegs m' MB (mbuf_cells A len cap) -> bytes_at asegs m' A bs -> mem_inv asegs m' ->
    cur0 <= cur' <= len ->
    vinv q' cur' G' cs' m'.
  Proof.
    intros q' cur G cs cur' G' cs' m m' (ST & SCR & TOK & SC & MBC & BUF & MI & AE & SHS & SHMB & SHA & SHSEP & SHFMT & SHZ & CR & QBA & VR) MUL WML ST' SCR' TOK' SC' MBC' BUF' MI' CR'.
    pose proof (WL_app q') as WA. pose proof VOK as VOK'. vokA VOK'.
    unfold vinv. repeat (split; [assumption|]).
    split; [exact (asan_env_frame asegs m m' (WL q') AE MUL WML (WL_env q'))|].
    split; [exact (shw_frame _ _ _ _ _ SHS MUL WA)|]. split; [exact (shw_frame _ _ _ _ _ SHMB MUL WA)|].
    split; [intros HL; exact (shw_frame _ _ _ _ _ (SHA HL) MUL WA)|].
    split; [exact (shw_frame _ _ _ _ _ SHSEP MUL WA)|]. split; [exact (shw_frame _ _ _ _ _ SHFMT MUL WA)|].
    split. { destruct (stack_window_lo FI lo CLO) as [S1 _]. pose proof (stack_lo_ok lo). pose proof (sh_hi_ok q QHI).
             eapply shz_frame; [exact SHZ| lia| lia| exact MUL| exact WA]. }
    split; [exact CR'|]. split; [exact QBA|]. exact (vrest_step q' m m' VR MUL WML).
  Qed.

  #[using="HC FI MB A len cap cur0 bs st m0 VOK RF0"] Lemma shz_stepV : forall q' m m', shz m (sh lo) (sh q) -> munch (WL q') m m' -> shz m' (sh lo) (sh q).
  Proof.
    intros q' m m' SHZ MUL. pose proof VOK as VOK'. vokA VOK'.
    destruct (stack_window_lo FI lo CLO) as [S1 _]. pose proof (stack_lo_ok lo). pose proof (sh_hi_ok q QHI).
    eapply shz_frame; [exact SHZ| lia| lia| exact MUL| exact (WL_app q')].
  Qed.
  #[using="HC FI q MB A len cap cur0 bs st m0 VOK RF0"] Lemma shw_stepV : forall q' m m' X n, shw m X n -> munch (WL q') m m' -> shw m' X n.
  Proof. intros q' m m' X n H MUL. exact (shw_frame _ _ _ _ _ H MUL (WL_app q')). Qed.

  #[using="Type"] Lemma contV : forall (q' r fp' c : Z) (b : byte) x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x25 x26 x27 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    acc m fp' -> ov_read_bytes asegs m (wa fp') 1 = Some [b] -> bv_unsigned b = c -> 0 < fp' < 2^62 -> 0 <= r <= 5 ->
    (r = 4 -> c <> 0 -> forall y1 y5 y6 y7 y12 y13 y14 y15 y16 y17 y18 y26 y27 y28 y29 y30 y31,
       evt asegs Q (headstA q' fp' c y1 y5 y6 y7 y12 y13 y14 y15 y16 y17 y18 y26 y27 y28 y29 y30 y31 m)) ->
    (r = 4 -> c = 0 -> forall y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31,
       evt asegs Q (epistA q' 4 y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 m)) ->
    (r <> 4 -> forall y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y24 y25 y26 y27 y28 y29 y30 y31,
       evt asegs Q (errstA q' r y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y24 y25 y26 y27 y28 y29 y30 y31 m)) ->
    evt asegs Q (contstA q' r fp' x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x25 x26 x27 x28 x29 x30 x31 m).
  Proof.
    intros q' r fp' c b x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x25 x26 x27 x28 x29 x30 x31 m Q HACC RD HB FPR RR KH KP KE.
    unfold contstA, vSHC. pose proof (bv_unsigned_in_range 8 b) as BR; unfold bv_modulus in BR; cbn in BR. rewrite HB in BR.
    zstep. step. ubr.
    zstep. zstep.
    acc_chk 11 fp' HACC k SHR Hk.
    step.
    gen2 CONT 0x86c9c 11%nat 12%nat.
    2:{ destruct Hk as [-> | [K1 K2]].
        - step. lit_branch. apply CONT.
        - rewrite sxb_small by lia. step. if_cases KB; zify_cond KB. 2:{ exfalso; lia. }
          zstep. step. if_cases KC; zify_cond KC; zify_granule KC; [apply CONT| exfalso; lia]. }
    intros ya1 ya2. clear SHR Hk HACC.
    zstep. cbn beta. rewrite HB.
    step. if_cases KZ; zify_cond KZ.
    -
      rewrite ?Z.mod_small in KZ by lia.
      destruct (Z.eq_dec r 4) as [-> | NE].
      + zstep. step. lit_branch. apply KP; [reflexivity| exact KZ].
      + apply KE. exact NE.
    - rewrite ?Z.mod_small in KZ by lia.
      step. if_cases KR; zify_cond KR.
      + apply KE. lia.
      + assert (r = 4) by lia. subst r. apply KH; [reflexivity| exact KZ].
  Qed.

  #[using="STACK_MALLOC_1 VOK RF0 FCO FE0"] Lemma prologueV : forall (fp0 c0 G : Z) (b0 : byte) t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (Q : machine_state -> Prop),
    stk asegs m0 lo q ->
    rw_cells asegs m0 S [C8 (wz MB); C8 (wz cur0); C4 (wz 0)] -> rw_cells asegs m0 MB (mbuf_cells A len cap) -> bytes_at asegs m0 A bs ->
    mem_inv asegs m0 -> asan_env asegs m0 ->
    shw m0 S 24 -> shw m0 MB 32 -> (0 < len -> shw m0 A len) -> shw m0 SEPTAB_A 20 -> shw m0 FMT flen ->
    shz m0 (sh lo) (sh q) ->
    FMT <= fp0 -> fp0 < FMT + flen -> 0x10000 <= FMT -> FMT + flen <= 0x609000 ->
    (forall m, mem_inv asegs m -> ov_read_bytes asegs m (wa fp0) 1 = Some [b0]) -> bv_unsigned b0 = c0 -> c0 <> 0 ->
    (forall q' m x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31, vinv q' cur0 G 1 m ->
       munch ((lo, q) :: FSIV []) m0 m -> wmono asegs m0 m -> fkeep FI [] st m0 m ->
       evt asegs Q (headstA q' fp0 c0 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m)) ->
    evt asegs Q
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz S) (wz fp0) (wz G) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz vfmatch_entryA) fc None m0 (seg_rom asegs)).
  Proof.
    intros fp0 c0 G b0 t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Q ST SC MBC BUF MI AG SHS SHMB SHA SHSEP SHFMT SHZ FP1 FP2 FMT0 FMTHI RD0 HB0 C0 K.
    eapply (prologue0V fp0 G); try eassumption.
    intros q' m x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x25 x26 x27 x28 x29 x30 x31 INV MUF WM FK.
    pose proof INV as (_ & _ & _ & _ & _ & _ & MIm & _ & _ & _ & _ & _ & SHFm & _).
    eapply (contV q' 4 fp0 c0 b0); [exact (proj1 SHFm fp0 ltac:(lia))| exact (RD0 m MIm)| exact HB0| lia| lia| | |].
    - intros _ _ y1 y5 y6 y7 y12 y13 y14 y15 y16 y17 y18 y26 y27 y28 y29 y30 y31. apply K; assumption.
    - intros _ E. exfalso. exact (C0 E).
    - intros E. exfalso. apply E. reflexivity.
  Qed.

  #[using="Type"] Lemma pctV : forall (q' fp c2 G cs : Z) (b2 : byte) x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    vscr q' G cs m -> mem_inv asegs m -> vjt_char c2 = true ->
    acc m (fp + 1) -> ov_read_bytes asegs m (wa (fp + 1)) 1 = Some [b2] -> bv_unsigned b2 = c2 -> 0 <= fp < 2^62 ->
    (forall y1 y5 y6 y7 y13 y14 y15 y16 y17 y18 y27 y28 y29 y30 y31,
       evt asegs Q (MS (mkR y1 (wz q') gp tp y5 y6 y7 (wz q) (wz q') (wz 4) (wz (vjt_off_A c2 + VJT_A)) (wz 88) y13 y14 y15 y16 y17
                            y18 (wz S) (wz 4) (wz 1) (wz 2147450880) (wz SHC) (wz (fp + 2)) (wz c2) (wz (F + 64)) y27 y28 y29 y30 y31)
                       F_ (wz (vjt_off_A c2 + VJT_A)) fc None m (seg_rom asegs))) ->
    evt asegs Q (headstA q' fp 37 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m).
  Proof.
    intros q' fp c2 G cs b2 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m Q (w0 & w16 & w32 & SCR) MI VC HACC RD HB FPR K.
    unfold headstA, vSHC.
    assert (CR : 32 <= c2 <= 120).
    { unfold vjt_char in VC. repeat (apply orb_prop in VC; destruct VC as [VC|VC]); try (apply Z.eqb_eq in VC; lia). }
    pose proof (vjt_read_A m c2 MI VC) as TR.
    zstep. step. lit_branch. zstep. step. lit_branch. zstep. step. lit_branch.
    zstep. step. ubr.
    zstep. zstep.
    acc_chk 10 (fp + 1) HACC k SHR Hk.
    step.
    gen2 CONT 0x86cd8 10%nat 11%nat.
    2:{ destruct Hk as [-> | [K1 K2]].
        - step. lit_branch. apply CONT.
        - rewrite sxb_small by lia. step. if_cases KB; zify_cond KB. 2:{ exfalso; lia. }
          zstep. step. if_cases KC; zify_cond KC; zify_granule KC; [apply CONT| exfalso; lia]. }
    intros ya0 ya1. clear SHR Hk HACC.
    zstep. cbn beta. rewrite HB. zstep. zstep. zstep. zstep. step. if_cases KD; zify_cond KD. { exfalso. lia. }
    replace (wa (VJT_A + 4 * (c2 - 32))) with (Z_to_bv 64 (Z.shiftl (c2 + -32) 2 + VJT_A))%Z in TR
      by (unfold wa; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    assert (OFF : (0 <= vjt_off_A c2 < 2^20)%Z /\ (vjt_off_A c2 + VJT_A) mod 2 = 0) by (unfold vjt_off_A; repeat (destruct (Z.eqb _ _)); cbn; lia).
    zstep. zstep. zstep. zstep. zstep. rewrite sx32_lit by lia. zstep. zstep. zstep.
    zstep. rewrite ret_pc_even by lia. apply K.
  Qed.

  #[using="IC FI cur0 st Wx VOK"] Lemma sgt_callV : forall (q' T TY cur : Z) (tw1 tw2 tyw : word)
      (ra' gp' tp' t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3 t4 t5 t6 : word) (m : mem),
    rw_cells asegs m S [C8 (wz MB); C8 (wz cur); C4 (wz 0)] -> rw_cells asegs m MB (mbuf_cells A len cap) -> bytes_at asegs m A bs ->
    0 <= cur <= len ->
    rw_cells asegs m T [C8 tw1; C8 tw2] -> rw_cells asegs m TY [C4 tyw] ->
    asan_env asegs m -> shw m S 24 -> shw m MB 32 -> shw m T 16 -> shw m TY 4 -> (0 < len -> shw m A len) -> shw m SEPTAB_A 20 ->
    0x609000 <= T -> (q' <= T \/ T + 16 <= alloc_ceiling) -> T mod 8 = 0 -> q' <= TY -> TY mod 4 = 0 ->
    (T + 16 <= TY \/ TY + 4 <= T) -> (T + 16 <= MB \/ S + 24 <= T) -> (T + 16 <= A \/ A + Z.of_nat (length bs) <= T) ->
    stk asegs m lo q' -> q + -304 <= q' <= q + -288 -> mem_inv asegs m ->
    a0 = wz S -> a1 = wz T -> a2 = wz TY ->
    evt asegs (sgt_post_A ra' q' gp' tp' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' F_ fc S T TY MB A cur len lo bs tyw m)
        (MS (mkR ra' (wz q') gp' tp' t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3 t4 t5 t6)
            F_ (wz sgt_entryA) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros SC MBC BUF CUR TC TYC AE SHS SHMB SHT SHTY SHA SHSEP T1 T2 T3 TY1 TY2 TT TP TA ST QB MI -> -> ->.
    pose proof VOK as VOK'. vokA VOK'. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    eapply (scanner_get_token_spec_A IC S T TY MB A cur len cap lo bs tw1 tw2 tyw q'); try eassumption; try reflexivity; try (unfold A0_RT_STACK; lia).
  Qed.

  #[using="HC FI S MB A len cap cur0 bs st Wx VOK"] Lemma tok_shw : forall q' m X n, shz m (sh lo) (sh q) -> q + -304 <= q' <= q + -288 -> q' + 8 <= X -> X + n <= q' + 184 -> 0 <= n -> shw m X n.
  Proof.
    intros q' m X n SHZ QB H1 H2 Hn. pose proof VOK as VOK'. vokA VOK'. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    eapply (shw_of_shz m (sh lo) (sh q) X n SHZ).
    - unfold win_ok. split; [exact Hn|]. right. change (2^47) with 140737488355328 in *. lia.
    - unfold sh, SHADOW_OFF. clear - H1 QB LO. Z.div_mod_to_equations. lia.
    - unfold sh, SHADOW_OFF. clear - H2 QB. Z.div_mod_to_equations. lia.
  Qed.

  Ltac open_vinv INV :=
    destruct INV as (ST & (w0 & w16 & w32 & SCR) & (j136 & tyA & tbA & tlA & j160 & tyB & tbB & tlB & TOK) & SC & MBC & BUF & MI & AE & SHS & SHMB & SHA & SHSEP & SHFMT & SHZ & CR & (QB & QAL) & VR);
    unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in MBC; hide QAL.

  #[using="IC VOK RF0"] Lemma dir_cV : forall (q' fp G cs cur : Z) (b2 : byte) x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    vinv q' cur G cs m ->
    acc m (fp + 1) -> ov_read_bytes asegs m (wa (fp + 1)) 1 = Some [b2] -> bv_unsigned b2 = 99 -> 0 <= fp < 2^62 ->
    (forall (r cur' : Z) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m',
       vinv q' cur' G cs m' -> munch (WP q' []) m m' -> wmono asegs m m' -> 0 <= r <= 5 -> (r = 4 -> cur + 1 <= cur') ->
       evt asegs Q (contstA q' r (fp + 2) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m')) ->
    (forall (r cur' : Z) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y24 y25 y26 y27 y28 y29 y30 y31 m',
       vinv q' cur' G cs m' -> munch (WP q' []) m m' -> wmono asegs m m' -> 0 <= r <= 5 -> r <> 4 ->
       evt asegs Q (errstA q' r y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y24 y25 y26 y27 y28 y29 y30 y31 m')) ->
    evt asegs Q (headstA q' fp 37 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m).
  Proof.
    intros q' fp G cs cur b2 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m Q INV HACC RD HB FPR KC KE.
    pose proof INV as INV0.
    eapply (pctV q' fp 99 G cs b2); [exact (proj1 (proj2 INV))| exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))) | reflexivity| exact HACC| exact RD| exact HB| exact FPR|].
    intros y1 y5 y6 y7 y13 y14 y15 y16 y17 y18 y27 y28 y29 y30 y31. cbn [vjt_off_A Z.eqb Pos.eqb Z.add].
    open_vinv INV.
    pose proof (munch_refl (WL q') m) as MUL. pose proof (munch_refl (WP q' []) m) as MUP. unfold vWP in MUP. pose proof (wmono_refl asegs m) as WML.
    pose proof VOK as VOK'; destruct VOK' as (CLO & LO & _ & QHI & MBLO & MBS & SHI & _ & _ & _ & A0 & AHI & LBS & CAP & ACAP & CUR0 & TXP & _ & _ & _ & _ & _).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    unfold vSHC, vSHE in *.
    zstep. zstep. zstep. step.
    split_chunk TOK 1%nat TKP TOK1. split_chunk TOK1 1%nat TYA TOK2. split_chunk TOK2 2%nat TKA TKR.
    eapply evt_cut.
    { eapply (sgt_callV q' (q' + 144) (q' + 140) cur); try eassumption; try reflexivity;
        first [ (eapply (tok_shw q'); [exact SHZ| exact QB| lia| lia| lia]) | (unhide QAL; clear - QAL; Z.div_mod_to_equations; lia) | lia ]. }
    unfold vWL in MUL. post_call asegs m.
    rename PC into ST. rename PC1 into SC. rename PC2 into TKA. rename PC3 into TYA. rename POST into RES. rename PC0 into AE'. rename MI0 into MI.
    lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?r) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => rename r into rr end.
    unfold PARSE_OK, PARSE_INCOMPLETE, PARSE_FAILURE in RES.
    destruct RES as [(tlz & ty & HR & -> & -> & -> & TL1 & -> & CL & TY5 & STRICT & CRB & CRL)|(HR & -> & ->)].
    - subst rr. step. lit_branch. zstep. rewrite (sx32_lit ty) by lia. zstep. step. zstep. zstep. step.
      join_chunks TYA TKA J1. join_chunks TKP J1 J2. join_chunks J2 TKR TOK.
      assert (INV' : vinv q' (cur + tlz) G cs _)
        by (eapply (vinv_step q' cur G cs (cur + tlz) G cs m _ INV0 MUL WML); [exact ST| do 3 eexists; exact SCR| do 8 eexists; exact TOK| exact SC| unfold mbuf_cells, MEMBUF_DEF_SIZE_INC; exact MBC| exact BUF| exact MI| lia]).
      match goal with |- context [Z_to_bv 64 (Z.lxor (Z.b2z ?bb) 5)] => replace (Z.lxor (Z.b2z bb) 5) with (if bb then 4 else 5) by (destruct bb; reflexivity); destruct bb end.
      + apply (KC 4 (cur + tlz)); [exact INV'| exact MUP| exact WML| lia| lia].
      + apply (KC 5 (cur + tlz)); [exact INV'| exact MUP| exact WML| lia| lia].
    - step. if_cases KB; zify_cond KB. 2:{ exfalso. lia. }

      join_chunks TYA TKA J1. join_chunks TKP J1 J2. join_chunks J2 TKR TOK.
      apply (KC rr cur); [| exact MUP| exact WML| lia| lia].
      eapply (vinv_step q' cur G cs cur G cs m _ INV0 MUL WML); [exact ST| do 3 eexists; exact SCR| do 8 eexists; exact TOK| exact SC| unfold mbuf_cells, MEMBUF_DEF_SIZE_INC; exact MBC| exact BUF| exact MI| lia].
  Qed.

  Ltac sgtA q' cur :=
    lazymatch goal with TOK : rw_cells asegs _ (q' + 136)%Z _ |- _ => let TKP := fresh "TKP" in let TOK1 := fresh "TOK1" in split_chunk TOK 1%nat TKP TOK1 end;
    lazymatch goal with TOK1 : rw_cells asegs _ (q' + 140)%Z _ |- _ => let TYA := fresh "TYA" in let TOK2 := fresh "TOK2" in split_chunk TOK1 1%nat TYA TOK2 end;
    lazymatch goal with TOK2 : rw_cells asegs _ (q' + 144)%Z _ |- _ => let TKA := fresh "TKA" in let TKR := fresh "TKR" in split_chunk TOK2 2%nat TKA TKR end;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
    eapply evt_cut;
    [ eapply (sgt_callV q' (q' + 144) (q' + 140) cur); try eassumption; try reflexivity;
        first [ (eapply (tok_shw q'); [eassumption| eassumption| lia| lia| lia]) | (match goal with QAL : hid (q' mod 16 = 0) |- _ => let Q2 := fresh in pose proof QAL as Q2; unfold hid in Q2; clear - Q2 end; Z.div_mod_to_equations; lia) | lia ]
    | unfold vWL, vWP in *; post_call asegs m;
      rename PC into ST; rename PC1 into SC; rename PC2 into TKA; rename PC3 into TYA; rename POST into RES; try (match goal with H : asan_env asegs m |- _ => clear H end); rename PC0 into AE; rename MI0 into MI;
      try rename rr into rr';
      lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?r) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => rename r into rr end;
      unfold PARSE_OK, PARSE_INCOMPLETE, PARSE_FAILURE in * ] end.
  Ltac joinA q' :=
    match goal with TYA : rw_cells asegs ?m (q' + 140)%Z _, TKA : rw_cells asegs ?m (q' + 144)%Z _ |- _ => let J1 := fresh "J1" in join_chunks TYA TKA J1 end;
    match goal with TKP : rw_cells asegs ?m (q' + 136)%Z _, J1 : rw_cells asegs ?m (q' + 140)%Z _ |- _ => let J2 := fresh "J2" in join_chunks TKP J1 J2 end;
    match goal with J2 : rw_cells asegs ?m (q' + 136)%Z _, TKR : rw_cells asegs ?m (q' + 160)%Z _ |- _ => let TOK := fresh "TOK" in join_chunks J2 TKR TOK end.
  Ltac close_vinv q' cur G cs cur' G' cs' m INV0 :=
    eapply (vinv_step q' cur G cs cur' G' cs' m _ INV0); [eassumption| eassumption| eassumption| do 3 eexists; eassumption| do 8 eexists; eassumption| eassumption
      | unfold mbuf_cells, MEMBUF_DEF_SIZE_INC; eassumption| eassumption| eassumption| lia].
  Ltac status5 := match goal with |- context [Z_to_bv 64 (Z.lxor (Z.b2z ?bb) 5)] => replace (Z.lxor (Z.b2z bb) 5) with (if bb then 4 else 5) by (destruct bb; reflexivity); destruct bb end.
  Ltac load_txp := pose proof VOK as VOK2; destruct VOK2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TXP & _).
  Ltac dir_intro q' INV := pose proof INV as INV0; open_vinv INV;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => pose proof (munch_refl (WL q') m) as MUL; pose proof (munch_refl (WP q' []) m) as MUP; unfold vWP in MUP; pose proof (wmono_refl asegs m) as WML end;
    pose proof VOK as VOK'; destruct VOK' as (CLO & LO & _ & QHI & MBLO & MBS & SHI & _ & _ & _ & A0 & AHI & LBS & CAP & ACAP & CUR0 & TXP & _ & _ & _ & _ & _);
    pose proof alloc_ceiling_range as ACR; unfold alloc_floor, alloc_ceiling_max in *; unfold vSHC, vSHE, vWP in *.

  #[using="IC VOK RF0"] Lemma dir_wV : forall (q' fp G cs cur : Z) (b2 : byte) x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    vinv q' cur G cs m ->
    acc m (fp + 1) -> ov_read_bytes asegs m (wa (fp + 1)) 1 = Some [b2] -> bv_unsigned b2 = 119 -> 0 <= fp < 2^62 ->
    (forall (r cur' : Z) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m',
       vinv q' cur' G cs m' -> munch (WP q' []) m m' -> wmono asegs m m' -> 0 <= r <= 5 -> (r = 4 -> cur <= cur') ->
       evt asegs Q (contstA q' r (fp + 2) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m')) ->
    (forall (r cur' : Z) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y24 y25 y26 y27 y28 y29 y30 y31 m',
       vinv q' cur' G cs m' -> munch (WP q' []) m m' -> wmono asegs m m' -> 0 <= r <= 5 -> r <> 4 ->
       evt asegs Q (errstA q' r y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y24 y25 y26 y27 y28 y29 y30 y31 m')) ->
    evt asegs Q (headstA q' fp 37 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m).
  Proof.
    intros q' fp G cs cur b2 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m Q INV HACC RD HB FPR KC KE.
    eapply (pctV q' fp 119 G cs b2); [exact (proj1 (proj2 INV))| exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))) | reflexivity| exact HACC| exact RD| exact HB| exact FPR|].
    intros y1 y5 y6 y7 y13 y14 y15 y16 y17 y18 y27 y28 y29 y30 y31. cbn [vjt_off_A Z.eqb Pos.eqb Z.add].
    dir_intro q' INV.
    zstep. zstep. zstep. step.
    sgtA q' cur.
    destruct RES as [(tlz & ty & HR & -> & -> & -> & TL1 & -> & CL & TY5 & STRICT & CRB & CRL)|(HR & -> & ->)].
    - subst rr. step. lit_branch. zstep. rewrite (sx32_lit ty) by lia. zstep. step. if_cases KW; zify_cond KW.
      +
        joinA q'. apply (KC 4 (cur + tlz)); [| eassumption| eassumption| lia| lia]. close_vinv q' cur G cs (cur + tlz) G cs m INV0.
      +
        pose proof (shw_frame _ _ _ _ _ SHS MUL (WL_app q')) as SHSn.
        cstep. cstep. zstep. zstep. zstep. zstep. sstep. zstep. step.
        replace (cur + tlz - tlz) with cur in * by lia.
        joinA q'. apply (KC 4 cur); [| eassumption| eassumption| lia| lia]. close_vinv q' cur G cs cur G cs m INV0.
    - step. if_cases KB; zify_cond KB. 2:{ exfalso. lia. }

      joinA q'. apply (KC rr cur); [| eassumption| eassumption| lia| lia]. close_vinv q' cur G cs cur G cs m INV0.
  Qed.

  #[using="IC VOK RF0"] Lemma dir_tabV : forall (q' fp G cs cur : Z) x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    vinv q' cur G cs m -> 0 <= fp < 2^62 ->
    (forall (r cur' : Z) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m',
       vinv q' cur' G cs m' -> munch (WP q' []) m m' -> wmono asegs m m' -> 0 <= r <= 5 -> (r = 4 -> cur + 1 <= cur') ->
       evt asegs Q (contstA q' r (fp + 1) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m')) ->
    (forall (r cur' : Z) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y24 y25 y26 y27 y28 y29 y30 y31 m',
       vinv q' cur' G cs m' -> munch (WP q' []) m m' -> wmono asegs m m' -> 0 <= r <= 5 -> r <> 4 ->
       evt asegs Q (errstA q' r y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y24 y25 y26 y27 y28 y29 y30 y31 m')) ->
    evt asegs Q (headstA q' fp 9 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m).
  Proof.
    intros q' fp G cs cur x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m Q INV FPR KC KE.
    unfold headstA. dir_intro q' INV.
    zstep. step. lit_branch.
    zstep. zstep. zstep. step.
    sgtA q' cur.
    destruct RES as [(tlz & ty & HR & -> & -> & -> & TL1 & -> & CL & TY5 & STRICT & CRB & CRL)|(HR & -> & ->)].
    - subst rr. zstep. step. lit_branch. zstep. rewrite (sx32_lit ty) by lia. zstep. step. zstep. zstep. zstep. step.
      joinA q'.
      assert (INV' : vinv q' (cur + tlz) G cs _) by (close_vinv q' cur G cs (cur + tlz) G cs m INV0).
      status5.
      + apply (KC 4 (cur + tlz)); [exact INV'| eassumption| eassumption| lia| lia].
      + apply (KC 5 (cur + tlz)); [exact INV'| eassumption| eassumption| lia| lia].
    - zstep. step. if_cases KB; zify_cond KB. 2:{ exfalso. lia. }
      joinA q'. apply (KC rr cur); [| eassumption| eassumption| lia| lia]. close_vinv q' cur G cs cur G cs m INV0.
  Qed.

  #[using="VOK RF0"] Lemma dir_iV : forall (q' fp G cs cur : Z) (b2 : byte) x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    vinv q' cur G cs m ->
    acc m (fp + 1) -> ov_read_bytes asegs m (wa (fp + 1)) 1 = Some [b2] -> bv_unsigned b2 = 105 -> 0 <= fp < 2^62 ->
    (forall y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m',
       vinv q' cur G 0 m' -> munch (WP q' []) m m' -> wmono asegs m m' ->
       evt asegs Q (contstA q' 4 (fp + 2) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m')) ->
    evt asegs Q (headstA q' fp 37 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m).
  Proof.
    intros q' fp G cs cur b2 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m Q INV HACC RD HB FPR KC.
    eapply (pctV q' fp 105 G cs b2); [exact (proj1 (proj2 INV))| exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))) | reflexivity| exact HACC| exact RD| exact HB| exact FPR|].
    intros y1 y5 y6 y7 y13 y14 y15 y16 y17 y18 y27 y28 y29 y30 y31. cbn [vjt_off_A Z.eqb Pos.eqb Z.add].
    dir_intro q' INV. unfold vWL in MUL.
    sstep. zstep. step.
    apply KC; [| exact MUP| exact WML]. close_vinv q' cur G cs cur G 0 m INV0.
  Qed.

  #[using="Type"] Lemma In_disjoint : forall (W : list ivl) a b X n, In (a, b) W -> disjoint_from W X n -> X + n <= a \/ b <= X.
  Proof.
    induction W as [|[x y] W IH]; intros a b X n HI D; [destruct HI|]. cbn [disjoint_from] in D. destruct D as [D1 D2].
    destruct HI as [E|HI]; [inversion E; subst; exact D1| exact (IH a b X n HI D2)].
  Qed.
  #[using="Type"] Lemma outside_In : forall (W : list ivl) a b x, In (a, b) W -> outside W x -> ~ (a <= x < b).
  Proof.
    induction W as [|[x' y'] W IH]; intros a b x HI O; [destruct HI|]. cbn [outside] in O. destruct O as [O1 O2].
    destruct HI as [E|HI]; [inversion E; subst; exact O1| exact (IH a b x HI O2)].
  Qed.

  #[using="Type"] Lemma WL_out : forall q' P n m m', In (P, P + n) Wx ->
    munch ((lo, q' + 184) :: (S + 8, S + 16) :: (P, P + n) :: Wx) m m' -> munch (WL q') m m'.
  Proof.
    intros q' P n m m' HI MU. eapply munch_weaken; [| exact MU]. unfold vWL. intros x O. cbn [outside] in *.
    destruct O as (O1 & O2 & O3). split; [exact O1|]. split; [exact O2|]. split; [exact (outside_In Wx P (P + n) x HI O3)| exact O3].
  Qed.

  #[using="IC VOK RF0"] Lemma dir_sV : forall (q' fp G cs cur P : Z) (b2 : byte) (pw1 pw2 : word) x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    vinv q' cur G cs m ->
    acc m (fp + 1) -> ov_read_bytes asegs m (wa (fp + 1)) 1 = Some [b2] -> bv_unsigned b2 = 115 -> 0 <= fp < 2^62 ->
    rw_cells asegs m G [C8 (wz P)] -> shw m G 8 -> q <= G -> G + 8 <= 2^47 -> G mod 8 = 0 ->
    rw_cells asegs m P [C8 pw1; C8 pw2] -> shw m P 16 -> In (P, P + 16) Wx -> P mod 8 = 0 ->
    (forall (r cur' : Z) (pa pb : word) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m',
       vinv q' cur' (G + 8) cs m' -> munch (WP q' [(P, P + 16)]) m m' -> wmono asegs m m' -> 0 <= r <= 5 ->
       rw_cells asegs m' P [C8 pa; C8 pb] ->
       (r = 4 -> exists l, pa = wz (A + cur) /\ pb = wz l /\ 1 <= l /\ cur' = cur + l /\ cur' < len) ->
       evt asegs Q (contstA q' r (fp + 2) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m')) ->
    (forall (r cur' : Z) (pa pb : word) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y24 y25 y26 y27 y28 y29 y30 y31 m',
       vinv q' cur' G cs m' -> munch (WP q' [(P, P + 16)]) m m' -> wmono asegs m m' -> 0 <= r <= 5 -> r <> 4 ->
       rw_cells asegs m' P [C8 pa; C8 pb] ->
       evt asegs Q (errstA q' r y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y24 y25 y26 y27 y28 y29 y30 y31 m')) ->
    evt asegs Q (headstA q' fp 37 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m).
  Proof.
    intros q' fp G cs cur P b2 pw1 pw2 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m Q INV HACC RD HB FPR GC SHG GLO GHI GAL PC SHP PIN PAL KC KE.
    eapply (pctV q' fp 115 G cs b2); [exact (proj1 (proj2 INV))| exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))) | reflexivity| exact HACC| exact RD| exact HB| exact FPR|].
    intros y1 y5 y6 y7 y13 y14 y15 y16 y17 y18 y27 y28 y29 y30 y31. cbn [vjt_off_A Z.eqb Pos.eqb Z.add].

    assert (PF : 0x609000 <= P /\ P + 16 <= alloc_ceiling /\ (P + 16 <= MB \/ S + 24 <= P) /\ (P + 16 <= A \/ A + Z.of_nat (length bs) <= P)).
    { pose proof VOK as VOK'. vokA VOK'. rewrite Forall_forall in WXL. destruct (WXL _ PIN) as [LE [LB|ER]]; cbn [fst snd] in *; [| exfalso; clear - ER; lia].
      destruct (lb_in_fs _ _ LB) as [H1 H2]. pose proof (fsb_ok FI) as (B1 & B2 & _).
      pose proof (In_disjoint Wx P (P + 16) _ _ PIN WXP) as D1. pose proof (In_disjoint Wx P (P + 16) _ _ PIN WXT) as D2.
      clear - H1 H2 B1 B2 D1 D2 MBS. lia. }
    destruct PF as (PLO & PHI & PPAR & PTXT).
    dir_intro q' INV. pose proof GAL as GAL'. hide PAL. hide GAL.
    zstep.
    cstep. cstep. cstep. cstep.   clear GAL'.
    zstep. zstep. zstep. zstep. step.
    split_chunk TOK 1%nat TKP TOK1. split_chunk TOK1 1%nat TYA TKR.
    assert (MULP : munch ((lo, q' + 184) :: (S + 8, S + 16) :: (P, P + 16) :: Wx) m m) by apply munch_refl. clear MUL MUP.
    assert (MUP : munch ((lo, q' + 184) :: (S + 8, S + 16) :: [(P, P + 16)]) m m) by apply munch_refl.
    eapply evt_cut.
    { eapply (sgt_callV q' P (q' + 140) cur); try eassumption; try reflexivity;
        first [ (eapply (tok_shw q'); [eassumption| eassumption| lia| lia| lia]) | (match goal with QAL : hid (q' mod 16 = 0) |- _ => let Q2 := fresh in pose proof QAL as Q2; unfold hid in Q2; clear - Q2 end; Z.div_mod_to_equations; lia) | (unhide PAL; exact PAL) | lia ]. }
    post_call asegs m.
    rename PC0 into ST. rename PC2 into SC. rename PC3 into PC. rename PC4 into TYA. rename POST into RES. clear AE. rename PC1 into AE. rename MI0 into MI.
    lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?r) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => rename r into rr end.
    unfold PARSE_OK, PARSE_INCOMPLETE, PARSE_FAILURE in RES.
    destruct RES as [(tlz & ty & HR & -> & -> & -> & TL1 & -> & CL & TY5 & STRICT & CRB & CRL)|(HR & -> & ->)].
    - subst rr. sstep. step. lit_branch. zstep. rewrite (sx32_lit ty) by lia. step. zstep. zstep. sstep. step.
      join_chunks TYA TKR J1. join_chunks TKP J1 TOK. apply (WL_out q' P 16 _ _ PIN) in MULP. rename MULP into MUL.
      assert (INV' : vinv q' (cur + tlz) (G + 8) cs _) by (close_vinv q' cur G cs (cur + tlz) (G + 8) cs m INV0).
      match goal with |- context [Z_to_bv 64 (Z.lxor (Z.b2z ?bb) 5)] => replace (Z.lxor (Z.b2z bb) 5) with (if bb then 4 else 5) by (destruct bb; reflexivity); destruct bb eqn:EB end.
      + eapply (KC 4 (cur + tlz)); [exact INV'| eassumption| eassumption| lia| exact PC|].
        intros _. exists tlz. unfold TT_IDENTIFIER in STRICT. apply Z.ltb_lt in EB. repeat split; try reflexivity; try lia.
      + eapply (KC 5 (cur + tlz)); [exact INV'| eassumption| eassumption| lia| exact PC|]. intros X; exfalso; lia.
    - sstep. step. if_cases KB; zify_cond KB. 2:{ exfalso. lia. }

      join_chunks TYA TKR J1. join_chunks TKP J1 TOK. apply (WL_out q' P 16 _ _ PIN) in MULP. rename MULP into MUL.
      eapply (KC rr cur); [| eassumption| eassumption| lia| exact PC| intros X; exfalso; lia]. close_vinv q' cur G cs cur (G + 8) cs m INV0.
  Qed.

  #[using="HC FI q lo S MB A cap cur0 st Wx VOK"] Lemma nth_bsA : forall i, 0 <= i < len -> exists b, nth_error bs (Z.to_nat i) = Some b.
  Proof.
    pose proof VOK as VOK'. vokA VOK'.
    intros i Hi. destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E; [eexists; reflexivity|].
    apply nth_error_None in E. lia.
  Qed.
  #[using="Type"] Lemma byte_rangeA : forall b : byte, 0 <= bv_unsigned b < 256.
  Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. lia. Qed.

  Ltac load_anz := pose proof VOK as VOK3; destruct VOK3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ANZ).

  #[using="IC VOK RF0"] Lemma dir_litV : forall (q' fp c G cs cur : Z) x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    vinv q' cur G cs m -> 0 <= fp < 2^62 -> 0 <= cs <= 1 ->
    0 < c < 256 -> c <> 9 -> c <> 32 -> c <> 37 ->
    (forall (r : Z) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m',
       vinv q' (cur + 1) G cs m' -> munch (WP q' []) m m' -> wmono asegs m m' -> 0 <= r <= 5 ->
       evt asegs Q (contstA q' r (fp + 1) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m')) ->
    (forall y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31,
       evt asegs Q (contstA q' 1 (fp + 1) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m)) ->
    evt asegs Q (headstA q' fp c x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m).
  Proof.
    intros q' fp c G cs cur x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m Q INV FPR CS CRc N9 N32 N37 KC KI.
    unfold headstA. dir_intro q' INV. unfold vWL in MUL. load_anz.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    zstep. step. if_cases K1; zify_cond K1. { exfalso; lia. }
    zstep. step. if_cases K2; zify_cond K2. { exfalso; lia. }
    zstep. step. if_cases K3; zify_cond K3. 2:{ exfalso; lia. }
    clear K1 K2 K3.
    pose proof (proj1 SHS) as ACS. pose proof (proj1 SHMB) as ACM.
    acc_chk0 23 (S + 8) ACS. step. clear_shr. step. lit_branch.
    zstep. zstep. pose proof S_al as SAL. acc_chk0 10 S ACS. clear SAL. step. clear_shr. step. lit_branch.
    pose proof MB_al as MBAL.
    zstep. step. ubr. zstep. step. ubr.
    zstep. zstep. zstep. acc_chk0 13 (MB + 8) ACM. step. clear_shr. step. lit_branch.
    zstep. zstep. zstep. zstep.
    step. if_cases KN; zify_cond KN.
    {   apply KI. }
    zstep. zstep. acc_chk0 10 MB ACM. step. clear_shr. step. lit_branch.
    acc_chk0 23 (S + 8) ACS. step. clear_shr. step. lit_branch.
    clear ACS ACM MBAL.
    zstep. zstep. zstep. zstep. sstep.
    assert (APOS : 0 < A) by (apply ANZ; lia).
    step. ubr. zstep. zstep. zstep. step. ub_b2z. lit_branch_safe. step. ubr.
    destruct (nth_bsA cur ltac:(lia)) as [b0 Hb0]. pose proof (byte_rangeA b0) as BR0.
    pose proof (shw_frame _ _ _ _ _ (SHA ltac:(lia)) MUL (WL_app q')) as SHA1.
    pose proof (proj1 SHA1 (A + cur) ltac:(lia)) as HACC.
    zstep. zstep.
    acc_chk 12 (A + cur) HACC k SHR Hk.
    step.
    gen2 CONT 0x86ee0 12%nat 13%nat.
    2:{ destruct Hk as [-> | [K1 K2]].
        - step. lit_branch. apply CONT.
        - rewrite sxb_small by lia. step. if_cases KB; zify_cond KB. 2:{ exfalso; lia. }
          zstep. step. if_cases KC'; zify_cond KC'; zify_granule KC'; [apply CONT| exfalso; lia]. }
    intros ya2 ya3. clear SHR Hk HACC SHA1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8ro_read asegs mm A bs cur b0 (Z_to_bv 64 (A + cur)) BUF Hb0 ltac:(lia) eq_refl) as RD0 end.
    zstep. cbn beta. zstep.
    assert (INV' : vinv q' (cur + 1) G cs _) by (close_vinv q' cur G cs (cur + 1) G cs m INV0).
    step. if_cases KS; zify_cond KS.
    -
      assert (cs = 0) by lia. subst cs.
      zstep.
      step.
      eapply evt_cut; [eapply (ic_tolower IC) with (c := c); [lia| reflexivity| eassumption]|].
      lazymatch goal with |- forall _, leaf_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm _ -> _ => post_call asegs mm end.
      zstep. zstep. step.
      eapply evt_cut; [eapply (ic_tolower IC) with (c := bv_unsigned b0); [lia| reflexivity| eassumption]|].
      lazymatch goal with |- forall _, leaf_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm _ -> _ => post_call asegs mm end.
      sstep. zstep. zstep. zstep. zstep. step.
      clear INV'. assert (INV' : vinv q' (cur + 1) G 0 _) by (close_vinv q' cur G 0 (cur + 1) G 0 m INV0).
      status5.
      + apply (KC 4); [exact INV'| eassumption| eassumption| lia].
      + apply (KC 5); [exact INV'| eassumption| eassumption| lia].
    - zstep. step. zstep. zstep. zstep. step.
      status5.
      + apply (KC 4); [exact INV'| eassumption| eassumption| lia].
      + apply (KC 5); [exact INV'| eassumption| eassumption| lia].
  Qed.

  Ltac sgtB q' cur :=
    lazymatch goal with TOK : rw_cells asegs _ (q' + 136)%Z _ |- _ => let TKP := fresh "TKP" in let TOK1 := fresh "TOK1" in split_chunk TOK 5%nat TKP TOK1 end;
    lazymatch goal with TOK1 : rw_cells asegs _ (q' + 164)%Z _ |- _ => let TYB := fresh "TYB" in let TKB := fresh "TKB" in split_chunk TOK1 1%nat TYB TKB end;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
    eapply evt_cut;
    [ eapply (sgt_callV q' (q' + 168) (q' + 164) cur); try eassumption; try reflexivity;
        first [ (eapply (tok_shw q'); [eassumption| eassumption| lia| lia| lia]) | (match goal with QAL : hid (q' mod 16 = 0) |- _ => let Q2 := fresh in pose proof QAL as Q2; unfold hid in Q2; clear - Q2 end; Z.div_mod_to_equations; lia) | lia ]
    | unfold vWL, vWP in *; post_call asegs m;
      rename PC into ST; rename PC1 into SC; rename PC2 into TKB; rename PC3 into TYB; rename POST into RES; try (match goal with H : asan_env asegs m |- _ => clear H end); rename PC0 into AE; rename MI0 into MI;
      try rename rr into rr';
      lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?r) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => rename r into rr end;
      unfold PARSE_OK, PARSE_INCOMPLETE, PARSE_FAILURE in * ] end.
  Ltac joinB q' :=
    match goal with TYB : rw_cells asegs ?m (q' + 164)%Z _, TKB : rw_cells asegs ?m (q' + 168)%Z _ |- _ => let J1 := fresh "J1" in join_chunks TYB TKB J1 end;
    match goal with TKP : rw_cells asegs ?m (q' + 136)%Z _, J1 : rw_cells asegs ?m (q' + 164)%Z _ |- _ => let TOK := fresh "TOK" in join_chunks TKP J1 TOK end.

  Ltac shw_adv q' :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mb _) =>
    match goal with MUL : munch (_ :: _ :: Wx) ?ma mb |- _ =>
      repeat match goal with
      | H : shw ma ?X ?n |- _ => apply (shw_stepV q' ma mb X n) in H; [| exact MUL]
      | H : shz ma _ _ |- _ => apply (shz_stepV q' ma mb) in H; [| exact MUL]
      | H : 0 < len -> shw ma A len |- _ =>
          let H' := fresh "SHA" in assert (H' : 0 < len -> shw mb A len) by (let HL := fresh in intros HL; exact (shw_stepV q' ma mb A len (H HL) MUL)); clear H
      end
    end end.

  Definition spst (q' fp : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 : word) (m : mem) : machine_state :=
    MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') x10 x11 x12 x13 x14 x15 x16 x17
            x18 (wz S) (wz 4) (wz 1) (wz 2147450880) (wz SHC) (wz 2) (wz (fp + 1)) x26 x27 x28 x29 x30 x31)
       F_ (wz 0x86dd4) fc None m (seg_rom asegs).

  #[using="VOK"] Lemma sp_incV : forall (q' fp G cs cur : Z) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x24 x26 x27 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    vinv q' cur G cs m ->
    (forall y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31,
       evt asegs Q (contstA q' 1 (fp + 1) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m)) ->
    evt asegs Q (MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') x10 x11 x12 x13 x14 x15 x16 x17
                         x18 (wz S) (wz 4) (wz 1) (wz 2147450880) (wz SHC) x24 (wz (fp + 1)) x26 x27 x28 x29 x30 x31)
                    F_ (wz 0x86f0c) fc None m (seg_rom asegs)).
  Proof.
    intros q' fp G cs cur x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x24 x26 x27 x28 x29 x30 x31 m Q INV K.
    dir_intro q' INV.
    zstep.
    pose proof (proj1 SHS (S + 16 + 4 - 1) ltac:(lia)) as HACC.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let a := reg_val 10 in
      destruct (AWAuto2.acc_loadw mm (S + 16) 4 a ltac:(lia) ltac:(pose proof S_al as SAL; clear - SAL; Z.div_mod_to_equations; lia) ltac:(lia) HACC ltac:(shadow_addr_tac)) as (k & SHR & Hk) end.
    step.
    gen2 CONT 0x86f18 10%nat 11%nat.
    2:{ destruct Hk as [-> | [K1 K2]].
        - step. lit_branch. apply CONT.
        - rewrite sxb_small by lia. step. if_cases KB; zify_cond KB. 2:{ exfalso; lia. }
          zstep. step. if_cases KC'; zify_cond KC'; zify_granule KC'; [apply CONT| exfalso; lia]. }
    intros ya0 ya1. clear SHR Hk HACC.
    zstep. zstep. step. lit_branch. zstep. zstep. step. unfold contstA, vSHC in K. apply K.
  Qed.

  #[using="VOK RF0"] Lemma sp_restoreV : forall (q' fp G cs curx sv r : Z) x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x24 x26 x27 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    vinv q' curx G cs m -> cur0 <= sv <= len -> 0 <= r <= 5 ->
    (forall y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m',
       vinv q' sv G cs m' -> munch (WP q' []) m m' -> wmono asegs m m' ->
       evt asegs Q (contstA q' r (fp + 1) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m')) ->
    evt asegs Q (MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') (wz r) x11 x12 x13 x14 x15 x16 x17
                         (wz sv) (wz S) (wz 4) (wz 1) (wz 2147450880) (wz SHC) x24 (wz (fp + 1)) x26 x27 x28 x29 x30 x31)
                    F_ (wz 0x86ef8) fc None m (seg_rom asegs)).
  Proof.
    intros q' fp G cs curx sv r x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x24 x26 x27 x28 x29 x30 x31 m Q INV SV RR K.
    dir_intro q' INV. unfold vWL in MUL.
    pose proof (proj1 SHS) as ACS.
    acc_chk0 23 (S + 8) ACS. step. clear_shr. step. lit_branch. clear ACS.
    zstep. sstep.
    assert (INV' : vinv q' sv G cs _) by (close_vinv q' curx G cs sv G cs m INV0).
    step. if_cases KR; zify_cond KR.
    - zstep. unfold contstA, vSHC in K. apply K; [exact INV'| exact MUP| exact WML].
    - assert (r = 1) by lia. subst r.
      eapply (sp_incV q' fp G cs sv); [exact INV'|].
      intros. apply K; [exact INV'| exact MUP| exact WML].
  Qed.

  #[using="IC VOK RF0"] Lemma sp_loopV : forall (k : nat) (q' fp G cs cur curi : Z) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m mi (Q : machine_state -> Prop),
    len - curi < Z.of_nat k -> vinv q' curi G cs mi -> cur <= curi -> munch (WP q' []) m mi -> wmono asegs m mi ->
    (forall (r cur' : Z) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m',
       vinv q' cur' G cs m' -> munch (WP q' []) m m' -> wmono asegs m m' -> 0 <= r <= 5 -> (r = 4 -> cur <= cur') ->
       evt asegs Q (contstA q' r (fp + 1) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m')) ->
    evt asegs Q (spst q' fp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 mi).
  Proof.
    induction k as [|k IH]; intros q' fp G cs cur curi x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m mi Q HK INV CI MU0 WM0 K.
    { exfalso. destruct INV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CR & _). lia. }
    unfold spst. dir_intro q' INV.
    pose proof (proj1 SHS) as ACS.
    acc_chk0 23 (S + 8) ACS. step. clear_shr. step. lit_branch. clear ACS.
    zstep.
    zstep. zstep. zstep. step.
    sgtB q' curi.
    destruct RES as [(tlz & ty & HR & -> & -> & -> & TL1 & -> & CL & TY5 & STRICT & CRB & CRL)|(HR & -> & ->)].
    - subst rr. step. lit_branch. zstep. rewrite (sx32_lit ty) by lia.
      step. if_cases KT; zify_cond KT.
      +
        joinB q'. assert (INV1 : vinv q' (curi + tlz) G cs _) by (close_vinv q' curi G cs (curi + tlz) G cs mi INV0).
        step. if_cases KW; zify_cond KW.
        *
          zstep. eapply (sp_restoreV q' fp G cs (curi + tlz) curi 4); [exact INV1| lia| lia|].
          intros until m'. intros INVr MUr WMr. eapply (K 4 curi); [exact INVr| | | lia| lia].
          -- exact (munch_trans _ _ _ _ MU0 MUr).
          -- exact (wmono_trans _ _ _ _ WM0 WMr).
        *
          eapply (IH q' fp G cs cur (curi + tlz)); [lia| exact INV1| lia| | | exact K].
          -- exact MU0.
          -- exact WM0.
      +
        assert (ty = 2) by lia. subst ty.
        joinB q'.
        shw_adv q'.
        zstep. zstep. zstep. step.
        sgtB q' (curi + tlz).
        destruct RES as [(tlz2 & ty2 & HR & -> & -> & -> & TL2 & -> & CL2 & TY52 & STRICT2 & CRB2 & CRL2)|(HR & -> & ->)].
        * subst rr. step. lit_branch. zstep. rewrite (sx32_lit ty2) by lia. step.
          joinB q'. assert (INV2 : vinv q' (curi + tlz + tlz2) G cs _) by (close_vinv q' curi G cs (curi + tlz + tlz2) G cs mi INV0).
          step. if_cases KW; zify_cond KW.
          -- zstep. eapply (sp_restoreV q' fp G cs (curi + tlz + tlz2) curi 4); [exact INV2| lia| lia|].
             intros until m'. intros INVr MUr WMr. eapply (K 4 curi); [exact INVr| | | lia| lia].
             ++ exact (munch_trans _ _ _ _ MU0 MUr).
             ++ exact (wmono_trans _ _ _ _ WM0 WMr).
          -- eapply (IH q' fp G cs cur (curi + tlz + tlz2)); [lia| exact INV2| lia| | | exact K].
             ++ exact MU0.
             ++ exact WM0.
        * joinB q'. assert (INV2 : vinv q' (curi + tlz) G cs _) by (close_vinv q' curi G cs (curi + tlz) G cs mi INV0).
          step. if_cases KB; zify_cond KB. 2:{ exfalso. lia. }
          eapply (sp_restoreV q' fp G cs (curi + tlz) curi rr); [exact INV2| lia| lia|].
          intros until m'. intros INVr MUr WMr. eapply (K rr curi); [exact INVr| | | lia| lia].
          -- exact (munch_trans _ _ _ _ MU0 MUr).
          -- exact (wmono_trans _ _ _ _ WM0 WMr).
    -
      joinB q'. assert (INV1 : vinv q' curi G cs _) by (close_vinv q' curi G cs curi G cs mi INV0).
      rename MU0 into MU1. rename WM0 into WM1.
      step. if_cases KB; zify_cond KB. 2:{ exfalso. lia. }
      step. if_cases KI; zify_cond KI.
      +
        zstep. unfold contstA, vSHC in K. eapply (K rr curi); [exact INV1| exact MU1| exact WM1| lia| lia].
      + assert (rr = 1) by lia. subst rr. eapply (sp_incV q' fp G cs curi); [exact INV1|].
        intros. eapply (K 1 curi); [exact INV1| exact MU1| exact WM1| lia| lia].
  Qed.

  #[using="IC VOK RF0"] Lemma dir_spV : forall (q' fp G cs cur : Z) x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    vinv q' cur G cs m -> 0 <= fp < 2^62 ->
    (forall (r cur' : Z) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m',
       vinv q' cur' G cs m' -> munch (WP q' []) m m' -> wmono asegs m m' -> 0 <= r <= 5 -> (r = 4 -> cur <= cur') ->
       evt asegs Q (contstA q' r (fp + 1) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m')) ->
    evt asegs Q (headstA q' fp 32 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m).
  Proof.
    intros q' fp G cs cur x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m Q INV FPR K.
    unfold headstA, vSHC.
    zstep. step. lit_branch. zstep. step. lit_branch. zstep. step.
    pose proof INV as INV0. destruct INV0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CR & _).
    eapply (sp_loopV (Datatypes.S (Z.to_nat (len - cur))) q' fp G cs cur cur); [lia| exact INV| lia| apply munch_refl| apply wmono_refl| exact K].
  Qed.

  #[using="FI q lo len cap cur0 st m0 VOK RF0"] Lemma out_facts : forall P n, In (P, P + n) Wx -> 0 <= n -> (8 < n \/ 0x609000 <= P) ->
    0x609000 <= P /\ P + n <= alloc_ceiling /\ (P + n <= MB \/ S + 24 <= P) /\ (P + n <= A \/ A + Z.of_nat (length bs) <= P).
  Proof.
    intros P n PIN Hn NE. pose proof VOK as VOK'. vokA VOK'. rewrite Forall_forall in WXL. destruct (WXL _ PIN) as [LE [LB|ER]]; cbn [fst snd] in *; [| exfalso; clear - ER NE Hn; lia].
    destruct (lb_in_fs _ _ LB) as [H1 H2]. pose proof (fsb_ok FI) as (B1 & B2 & _).
    pose proof (In_disjoint Wx P (P + n) _ _ PIN WXP) as D1. pose proof (In_disjoint Wx P (P + n) _ _ PIN WXT) as D2.
    clear - H1 H2 B1 B2 D1 D2 MBS Hn. lia.
  Qed.

  #[using="IC VOK RF0"] Lemma L_loopV : forall (k : nat) (q' fp G cs cur curi P : Z) (pw2 : word) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 m mi (Q : machine_state -> Prop),
    len - curi < Z.of_nat k -> cur0 <= cur <= curi -> vinv q' curi G cs mi ->
    munch (WP q' [(P, P + 16)]) m mi -> wmono asegs m mi ->
    rw_cells asegs mi P [C8 (wz (A + cur)); C8 pw2] -> shw mi P 16 -> In (P, P + 16) Wx -> P mod 8 = 0 -> 0 <= fp < 2^62 ->
    (forall (r cur' : Z) (pb : word) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m',
       vinv q' cur' G cs m' -> munch (WP q' [(P, P + 16)]) m m' -> wmono asegs m m' -> 0 <= r <= 5 ->
       rw_cells asegs m' P [C8 (wz (A + cur)); C8 pb] ->
       (r = 4 -> exists l, pb = wz l /\ 0 <= l /\ cur' = cur + l /\ cur' < len
                  /\ exists b, nth_error bs (Z.to_nat cur') = Some b /\ (bv_unsigned b = 13 \/ bv_unsigned b = 10)) ->
       evt asegs Q (contstA q' r (fp + 2) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m')) ->
    evt asegs Q (MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') x10 x11 x12 x13 x14 x15 x16 x17
                         (wz cur) (wz S) (wz 4) (wz 1) (wz 2147450880) (wz SHC) (wz (fp + 2)) (wz P) (wz 2) x27 x28 x29 x30 x31)
                    F_ (wz 0x8726c) fc None mi (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros q' fp G cs cur curi P pw2 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 m mi Q HK CI INV MU0 WM0 PCH SHP PIN PAL FPR K.
    { exfalso. destruct INV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CR & _). lia. }
    destruct (out_facts P 16 PIN ltac:(lia) ltac:(left; lia)) as (PLO & PHI & PPAR & PTXT). hide PAL.
    dir_intro q' INV. clear MUL MUP. pose proof (munch_refl ((lo, q' + 184) :: (S + 8, S + 16) :: (P, P + 16) :: Wx)%Z mi) as MUL.
    zstep. zstep. zstep. step.
    sgtB q' curi.
    destruct RES as [(tlz & ty & HR & -> & -> & -> & TL1 & -> & CL & TY5 & STRICT & CRB & CRL)|(HR & -> & ->)].
    - subst rr. step. lit_branch. zstep. rewrite (sx32_lit ty) by lia.
      step. if_cases KT; zify_cond KT.
      +
        joinB q'. pose proof (WL_out q' P 16 _ _ PIN MUL) as MUW.
        assert (INV1 : vinv q' (curi + tlz) G cs _) by (clear MUL; close_vinv q' curi G cs (curi + tlz) G cs mi INV0).
        pose proof (shw_stepV q' _ _ P 16 SHP MUW) as SHP1.
        eapply (IH q' fp G cs cur (curi + tlz) P pw2); [lia| lia| exact INV1| exact MU0| exact WM0| exact PCH| exact SHP1| exact PIN| unhide PAL; exact PAL| exact FPR| exact K].
      +
        assert (ty = 2) by lia. subst ty.
        pose proof (shw_stepV q' _ _ S 24 SHS (WL_out q' P 16 _ _ PIN MUL)) as SHS1. pose proof (proj1 SHS1) as ACS.
        acc_chk0 23 (S + 8) ACS. step. clear_shr. step. lit_branch. clear ACS SHS1.
        zstep. zstep. zstep. zstep. zstep. zstep. sstep.
        replace (curi + tlz - tlz) with curi in * by lia.
        pose proof (shw_stepV q' _ _ P 16 SHP (WL_out q' P 16 _ _ PIN MUL)) as SHP1. pose proof (proj1 SHP1) as ACP.
        zstep. unhide PAL. acc_chk0 12 (P + 8) ACP. hide PAL. step. clear_shr. step. lit_branch. clear ACP SHP1.
        zstep. sstep. step.
        joinB q'. apply (WL_out q' P 16 _ _ PIN) in MUL.
        eapply (K 4 curi); [close_vinv q' curi G cs curi G cs mi INV0| exact MU0| exact WM0| lia| exact PCH|].
        intros _. exists (curi - cur). split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. apply (CRB eq_refl). lia.
    -
      joinB q'. apply (WL_out q' P 16 _ _ PIN) in MUL.
      step. if_cases KB; zify_cond KB. 2:{ exfalso. lia. }
      unfold contstA, vSHC in K. eapply (K rr curi); [close_vinv q' curi G cs curi G cs mi INV0| exact MU0| exact WM0| lia| exact PCH|].
      intros X; exfalso; lia.
  Qed.

  #[using="IC VOK RF0"] Lemma dir_LV : forall (q' fp G cs cur P : Z) (b2 : byte) (pw1 pw2 : word) x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    vinv q' cur G cs m ->
    acc m (fp + 1) -> ov_read_bytes asegs m (wa (fp + 1)) 1 = Some [b2] -> bv_unsigned b2 = 76 -> 0 <= fp < 2^62 ->
    rw_cells asegs m G [C8 (wz P)] -> shw m G 8 -> q <= G -> G + 8 <= 2^47 -> G mod 8 = 0 ->
    rw_cells asegs m P [C8 pw1; C8 pw2] -> shw m P 16 -> In (P, P + 16) Wx -> P mod 8 = 0 ->
    (forall (r cur' : Z) (pb : word) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m',
       vinv q' cur' (G + 8) cs m' -> munch (WP q' [(P, P + 16)]) m m' -> wmono asegs m m' -> 0 <= r <= 5 ->
       rw_cells asegs m' P [C8 (wz (A + cur)); C8 pb] ->
       (r = 4 -> exists l, pb = wz l /\ 0 <= l /\ cur' = cur + l /\ cur' < len
                  /\ exists b, nth_error bs (Z.to_nat cur') = Some b /\ (bv_unsigned b = 13 \/ bv_unsigned b = 10)) ->
       evt asegs Q (contstA q' r (fp + 2) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m')) ->
    evt asegs Q (headstA q' fp 37 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m).
  Proof.
    intros q' fp G cs cur P b2 pw1 pw2 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m Q INV HACC RD HB FPR GC SHG GLO GHI GAL PC SHP PIN PAL K.
    eapply (pctV q' fp 76 G cs b2); [exact (proj1 (proj2 INV))| exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))) | reflexivity| exact HACC| exact RD| exact HB| exact FPR|].
    intros y1 y5 y6 y7 y13 y14 y15 y16 y17 y18 y27 y28 y29 y30 y31. cbn [vjt_off_A Z.eqb Pos.eqb Z.add].
    destruct (out_facts P 16 PIN ltac:(lia) ltac:(left; lia)) as (PLO & PHI & PPAR & PTXT).
    dir_intro q' INV. clear MUL MUP. pose proof (munch_refl ((lo, q' + 184) :: (S + 8, S + 16) :: (P, P + 16) :: Wx)%Z m) as MUL. pose proof (munch_refl ((lo, q' + 184) :: (S + 8, S + 16) :: [(P, P + 16)])%Z m) as MUP.
    pose proof (proj1 SHS) as ACS. pose proof (proj1 SHMB) as ACM. pose proof (proj1 SHP) as ACP. pose proof (proj1 SHG) as ACG.
    load_anz.
    zstep. zstep. zstep. acc_chk0 11 G ACG. step. clear_shr. step. lit_branch.
    acc_chk0 23 (S + 8) ACS. step. clear_shr. step. lit_branch.
    zstep. zstep. pose proof S_al as SAL. acc_chk0 10 S ACS. clear SAL. step. clear_shr. step. lit_branch.
    pose proof MB_al as MBAL.
    zstep. zstep. step. ubr. zstep. step. ubr.
    zstep. zstep. acc_chk0 11 MB ACM. step. clear_shr. step. lit_branch. clear MBAL.
    zstep. zstep. zstep. step. ubr.
    zstep. zstep. zstep.

    replace (Z.lxor (Z.b2z (0 <? A)) (Z.b2z (cur + A <? 1))) with 1.
    2:{ destruct (Z.ltb_spec 0 A) as [AP|AN].
        - replace (cur + A <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
        - replace (cur + A <? 1) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
    step. lit_branch.
    zstep. zstep. step. ubr. zstep. step. ubr.
    zstep. zstep. acc_chk0 11 P ACP. step. clear_shr. step. lit_branch.
    clear ACS ACM ACP ACG. hide PAL. hide GAL.
    zstep. zstep. sstep. sstep.
    replace (cur + A)%Z with (A + cur)%Z in * by lia.
    pose proof (WL_out q' P 16 _ _ PIN MUL) as MUW.
    assert (INV1 : vinv q' cur (G + 8) cs _) by (clear MUL; close_vinv q' cur G cs cur (G + 8) cs m INV0).
    pose proof (shw_stepV q' _ _ P 16 SHP MUW) as SHP1.
    eapply (L_loopV (Datatypes.S (Z.to_nat (len - cur))) q' fp (G + 8) cs cur cur P pw2); [lia| lia| exact INV1| exact MUP| exact WML| exact PC| exact SHP1| exact PIN| unhide PAL; exact PAL| exact FPR| exact K].
  Qed.

  Definition vscrW (q' G cs : Z) (w16 w32 : word) (m : mem) : Prop :=
    exists w0, rw_cells asegs m q' [C8 w0; C8 (wz (Z.land (S + 16) 7 + 3)); C8 w16; C8 (wz (F + 32)); C8 w32; C8 (wz cur0); C8 (wz VMASK); C8 (wz F); C8 (wz F);
                                     C8 (wz SF); C8 (wz SHE); C8 (wz (S + 16)); C8 (wz cs); C8 (wz (F + 64)); C8 (wz G); C8 (wz (S + 8)); C8 (wz F)].

  #[using="VOK RF0"] Lemma S_exit_errV : forall (q' fp G cs cur curi P rr : Z) (pb v8 : word) x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x25 x26 x27 x28 x29 x30 x31 m mi (Q : machine_state -> Prop),
    vinv q' curi G cs mi -> vscrW q' G cs v8 (wz cur) mi -> cur0 <= cur <= curi -> 0 <= rr <= 5 -> rr <> 4 ->
    munch (WP q' [(P, P + 16)]) m mi -> wmono asegs m mi ->
    rw_cells asegs mi P [C8 (wz (A + cur)); C8 pb] -> In (P, P + 16) Wx ->
    (forall (r cur' : Z) (pa pb : word) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m',
       vinv q' cur' G cs m' -> munch (WP q' [(P, P + 16)]) m m' -> wmono asegs m m' -> 0 <= r <= 5 ->
       rw_cells asegs m' P [C8 pa; C8 pb] ->
       (r = 4 -> exists l, pa = wz (A + cur) /\ pb = wz l /\ 1 <= l /\ cur' = cur + l /\ cur' < len) ->
       evt asegs Q (contstA q' r (fp + 2) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m')) ->
    evt asegs Q (MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') (wz rr) x11 x12 x13 x14 x15 x16 x17
                         x18 (wz S) (wz 4) (wz 1) (wz 2147450880) (wz SHC) (wz (fp + 2)) x25 x26 x27 x28 x29 x30 x31)
                    F_ (wz 0x87468) fc None mi (seg_rom asegs)).
  Proof.
    intros q' fp G cs cur curi P rr pb v8 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x25 x26 x27 x28 x29 x30 x31 m mi Q INV (j0' & SCRW) CI RR RN MU0 WM0 PCH PIN K.
    destruct (out_facts P 16 PIN ltac:(lia) ltac:(left; lia)) as (PLO & PHI & PPAR & PTXT).
    dir_intro q' INV. clear MUL MUP SCR. rename SCRW into SCR. pose proof (munch_refl ((lo, q' + 184) :: (S + 8, S + 16) :: (P, P + 16) :: Wx)%Z mi) as MUL.

    gen2 CONT 0x87484 11%nat 12%nat.
    2:{ step. if_cases KI; zify_cond KI.
        - apply CONT.
        - assert (rr = 1) by lia. subst rr.
          zstep.
          pose proof (proj1 SHS (S + 16 + 4 - 1) ltac:(lia)) as HACC.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            let a := reg_val 11 in
            destruct (AWAuto2.acc_loadw mm (S + 16) 4 a ltac:(lia) ltac:(pose proof S_al as SAL; clear - SAL; Z.div_mod_to_equations; lia) ltac:(lia) HACC ltac:(shadow_addr_tac)) as (k & SHR & Hk) end.
          step.
          gen2 CONT2 0x87478 11%nat 12%nat.
          2:{ destruct Hk as [-> | [K1 K2]].
              - step. lit_branch. apply CONT2.
              - rewrite sxb_small by lia. step. if_cases KB; zify_cond KB. 2:{ exfalso; lia. }
                zstep. step. if_cases KC'; zify_cond KC'; zify_granule KC'; [apply CONT2| exfalso; lia]. }
          intros ya1 ya2. clear SHR Hk HACC.
          zstep. zstep. step. lit_branch. apply CONT. }
    intros ya1 ya2.
    pose proof (proj1 SHS) as ACS.
    acc_chk0 23 (S + 8) ACS. step. clear_shr. step. lit_branch. clear ACS.
    zstep. zstep. sstep. step.
    apply (WL_out q' P 16 _ _ PIN) in MUL.
    unfold contstA, vSHC in K. eapply (K rr cur); [| exact MU0| exact WM0| lia| exact PCH| intros X; exfalso; lia].
    close_vinv q' curi G cs cur G cs mi INV0.
  Qed.

  #[using="VOK RF0"] Lemma S_exit_okV : forall (q' fp G cs cur curi tlz P : Z) (v8 : word) x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m mi (Q : machine_state -> Prop),
    vinv q' (curi + tlz) G cs mi -> vscrW q' G cs v8 (wz cur) mi -> cur0 <= cur <= curi -> 1 <= tlz -> curi + tlz <= len ->
    munch (WP q' [(P, P + 16)]) m mi -> wmono asegs m mi ->
    rw_cells asegs mi P [C8 (wz (A + cur)); C8 (wz (curi - cur))] -> shw mi P 16 -> In (P, P + 16) Wx -> P mod 8 = 0 ->
    (forall (r cur' : Z) (pa pb : word) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m',
       vinv q' cur' G cs m' -> munch (WP q' [(P, P + 16)]) m m' -> wmono asegs m m' -> 0 <= r <= 5 ->
       rw_cells asegs m' P [C8 pa; C8 pb] ->
       (r = 4 -> exists l, pa = wz (A + cur) /\ pb = wz l /\ 1 <= l /\ cur' = cur + l /\ cur' < len) ->
       evt asegs Q (contstA q' r (fp + 2) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m')) ->
    evt asegs Q (MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') (wz tlz) x11 x12 x13 x14 x15 x16 x17
                         (wz (Z.shiftr (P + 8) 3 + 2147450880)) (wz S) (wz 4) (wz 1) (wz 2147450880) (wz SHC) (wz (fp + 2)) (wz 83) (wz P) (wz (P + 8)) x28 x29 x30 x31)
                    F_ (wz 0x875f8) fc None mi (seg_rom asegs)).
  Proof.
    intros q' fp G cs cur curi tlz P v8 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m mi Q INV (j0' & SCRW) CI TL1 CL MU0 WM0 PCH SHP PIN PAL K.
    destruct (out_facts P 16 PIN ltac:(lia) ltac:(left; lia)) as (PLO & PHI & PPAR & PTXT).
    dir_intro q' INV. clear MUL MUP SCR. rename SCRW into SCR. pose proof (munch_refl ((lo, q' + 184) :: (S + 8, S + 16) :: (P, P + 16) :: Wx)%Z mi) as MUL.
    pose proof (proj1 SHS) as ACS.
    acc_chk0 23 (S + 8) ACS. step. clear_shr. step. lit_branch. clear ACS.
    zstep. zstep. zstep. sstep.
    replace (curi + tlz - tlz) with curi in * by lia.
    pose proof (shw_stepV q' _ _ P 16 SHP (WL_out q' P 16 _ _ PIN MUL)) as SHP1. pose proof (proj1 SHP1) as ACP.
    acc_chk0 18 (P + 8) ACP. step. clear_shr. step. lit_branch. clear ACP SHP1. hide PAL.
    zstep. zstep. zstep. zstep. step. lit_branch.
    apply (WL_out q' P 16 _ _ PIN) in MUL.
    assert (INV1 : vinv q' curi G cs _) by (close_vinv q' (curi + tlz) G cs curi G cs mi INV0).
    unfold contstA, vSHC in K.
    match goal with |- context [Z_to_bv 64 (Z.lxor (Z.b2z ?bb) 5)] => replace (Z.lxor (Z.b2z bb) 5) with (if bb then 4 else 5) by (destruct bb; reflexivity); destruct bb eqn:EB end.
    - eapply (K 4 curi); [exact INV1| exact MU0| exact WM0| lia| exact PCH|].
      intros _. exists (curi - cur). repeat split; try reflexivity; try lia.
    - eapply (K 5 curi); [exact INV1| exact MU0| exact WM0| lia| exact PCH| intros X; exfalso; lia].
  Qed.

  #[using="VOK RF0"] Lemma S_bodyV : forall (q' fp G cs cur curi tlz ty P : Z) (v8 : word) x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m mi (Q : machine_state -> Prop),
    vinv q' (curi + tlz) G cs mi -> vscrW q' G cs v8 (wz cur) mi -> cur0 <= cur <= curi -> 1 <= tlz -> curi + tlz <= len -> 0 <= ty <= 5 ->
    munch (WP q' [(P, P + 16)]) m mi -> wmono asegs m mi ->
    rw_cells asegs mi P [C8 (wz (A + cur)); C8 (wz (curi - cur))] -> shw mi P 16 -> In (P, P + 16) Wx -> P mod 8 = 0 ->
    (forall (r cur' : Z) (pa pb : word) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m',
       vinv q' cur' G cs m' -> munch (WP q' [(P, P + 16)]) m m' -> wmono asegs m m' -> 0 <= r <= 5 ->
       rw_cells asegs m' P [C8 pa; C8 pb] ->
       (r = 4 -> exists l, pa = wz (A + cur) /\ pb = wz l /\ 1 <= l /\ cur' = cur + l /\ cur' < len) ->
       evt asegs Q (contstA q' r (fp + 2) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m')) ->
    (forall y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m',
       vinv q' (curi + tlz) G cs m' -> vscrW q' G cs v8 (wz cur) m' ->
       munch (WP q' [(P, P + 16)]) m m' -> wmono asegs m m' ->
       rw_cells asegs m' P [C8 (wz (A + cur)); C8 (wz (curi + tlz - cur))] -> shw m' P 16 ->
       evt asegs Q (MS (mkR y1 (wz q') gp tp y5 y6 y7 (wz q) (wz q') y10 y11 y12 y13 y14 y15 y16 y17
                         (wz (Z.shiftr (P + 8) 3 + 2147450880)) (wz S) (wz 4) (wz 1) (wz 2147450880) (wz SHC) (wz (fp + 2)) (wz 83) (wz P) (wz (P + 8)) y28 y29 y30 y31)
                    F_ (wz 0x87454) fc None m' (seg_rom asegs))) ->
    evt asegs Q (MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') (wz tlz) (wz ty) x12 x13 x14 x15 x16 x17
                         (wz (Z.shiftr (P + 8) 3 + 2147450880)) (wz S) (wz 4) (wz 1) (wz 2147450880) (wz SHC) (wz (fp + 2)) (wz 83) (wz P) (wz (P + 8)) x28 x29 x30 x31)
                    F_ (wz 0x87434) fc None mi (seg_rom asegs)).
  Proof.
    intros q' fp G cs cur curi tlz ty P v8 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m mi Q INV SCRW0 CI TL1 CL TY5 MU0 WM0 PCH SHP PIN PAL K KS2.
    zstep. zstep. step. if_cases KT; zify_cond KT.
    - eapply (S_exit_okV q' fp G cs cur curi tlz P v8); eassumption.
    - destruct (out_facts P 16 PIN ltac:(lia) ltac:(left; lia)) as (PLO & PHI & PPAR & PTXT).
      pose proof SCRW0 as SCRW. destruct SCRW as (j0' & SCRW).
      dir_intro q' INV. clear MUL MUP SCR. rename SCRW into SCR. pose proof (munch_refl ((lo, q' + 184) :: (S + 8, S + 16) :: (P, P + 16) :: Wx)%Z mi) as MUL.
      pose proof (proj1 SHP) as ACP.
      acc_chk0 18 (P + 8) ACP. step. clear_shr. step. lit_branch. clear ACP. hide PAL.
      zstep. zstep. sstep.
      pose proof (WL_out q' P 16 _ _ PIN MUL) as MUW.
      apply KS2; [clear MUL; close_vinv q' (curi + tlz) G cs (curi + tlz) G cs mi INV0| eexists; exact SCR| exact MU0| exact WM0| | exact (shw_stepV q' _ _ P 16 SHP MUW)].
      replace (curi + tlz - cur) with (curi - cur + tlz) by lia. exact PCH.
  Qed.

  #[using="IC VOK RF0"] Lemma S_loopV : forall (k : nat) (pc0 q' fp G cs cur curi P : Z) (v8 : word) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m mi (Q : machine_state -> Prop),
    len - curi < Z.of_nat k -> (pc0 = 0x87418 \/ pc0 = 0x87454) ->
    vinv q' curi G cs mi -> vscrW q' G cs v8 (wz cur) mi -> cur0 <= cur <= curi ->
    munch (WP q' [(P, P + 16)]) m mi -> wmono asegs m mi ->
    rw_cells asegs mi P [C8 (wz (A + cur)); C8 (wz (curi - cur))] -> shw mi P 16 -> In (P, P + 16) Wx -> P mod 8 = 0 -> 0 <= fp < 2^62 ->
    (forall (r cur' : Z) (pa pb : word) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m',
       vinv q' cur' G cs m' -> munch (WP q' [(P, P + 16)]) m m' -> wmono asegs m m' -> 0 <= r <= 5 ->
       rw_cells asegs m' P [C8 pa; C8 pb] ->
       (r = 4 -> exists l, pa = wz (A + cur) /\ pb = wz l /\ 1 <= l /\ cur' = cur + l /\ cur' < len) ->
       evt asegs Q (contstA q' r (fp + 2) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m')) ->
    evt asegs Q (MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') x10 x11 x12 x13 x14 x15 x16 x17
                         (wz (Z.shiftr (P + 8) 3 + 2147450880)) (wz S) (wz 4) (wz 1) (wz 2147450880) (wz SHC) (wz (fp + 2)) (wz 83) (wz P) (wz (P + 8)) x28 x29 x30 x31)
                    F_ (wz pc0) fc None mi (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros pc0 q' fp G cs cur curi P v8 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m mi Q HK SITE INV SCRW0 CI MU0 WM0 PCH SHP PIN PAL FPR K.
    { exfalso. destruct INV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CR & _). lia. }
    destruct (out_facts P 16 PIN ltac:(lia) ltac:(left; lia)) as (PLO & PHI & PPAR & PTXT). pose proof PAL as PAL'. hide PAL.
    pose proof SCRW0 as SCRW. destruct SCRW as (j0' & SCRW).
    dir_intro q' INV. clear MUL MUP SCR. rename SCRW into SCR. pose proof (munch_refl ((lo, q' + 184) :: (S + 8, S + 16) :: (P, P + 16) :: Wx)%Z mi) as MUL.
    assert (NEXT : forall y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 (tlz : Z) m',
       1 <= tlz -> vinv q' (curi + tlz) G cs m' -> vscrW q' G cs v8 (wz cur) m' ->
       munch (WP q' [(P, P + 16)]) m m' -> wmono asegs m m' ->
       rw_cells asegs m' P [C8 (wz (A + cur)); C8 (wz (curi + tlz - cur))] -> shw m' P 16 ->
       evt asegs Q (MS (mkR y1 (wz q') gp tp y5 y6 y7 (wz q) (wz q') y10 y11 y12 y13 y14 y15 y16 y17
                         (wz (Z.shiftr (P + 8) 3 + 2147450880)) (wz S) (wz 4) (wz 1) (wz 2147450880) (wz SHC) (wz (fp + 2)) (wz 83) (wz P) (wz (P + 8)) y28 y29 y30 y31)
                    F_ (wz 0x87454) fc None m' (seg_rom asegs))).
    { intros until m'. intros TL1 INVn SCRn MUn WMn PCn SHPn.
      eapply (IH 0x87454 q' fp G cs cur (curi + tlz) P v8); [lia| right; reflexivity| exact INVn| exact SCRn| lia| exact MUn| exact WMn| exact PCn| exact SHPn| exact PIN| exact PAL'| exact FPR| exact K]. }
    clear IH PAL'.
    destruct SITE as [-> | ->].
    - zstep. zstep. zstep. step.
      sgtB q' curi.
      destruct RES as [(tlz & ty & HR & -> & -> & -> & TL1 & -> & CL & TY5 & STRICT & CRB & CRL)|(HR & -> & ->)].
      + subst rr. step. lit_branch. zstep. rewrite (sx32_lit ty) by lia. zstep.
        joinB q'. pose proof (WL_out q' P 16 _ _ PIN MUL) as MUW.
        eapply (S_bodyV q' fp G cs cur curi tlz ty P v8); [clear MUL; close_vinv q' curi G cs (curi + tlz) G cs mi INV0| eexists; exact SCR| lia| lia| lia| lia| exact MU0| exact WM0| exact PCH
          | exact (shw_stepV q' _ _ P 16 SHP MUW)| exact PIN| unhide PAL; exact PAL| exact K|].
        intros. eapply (NEXT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tlz); eassumption.
      + joinB q'. pose proof (WL_out q' P 16 _ _ PIN MUL) as MUW.
        step. if_cases KB; zify_cond KB. 2:{ exfalso. lia. }
        eapply (S_exit_errV q' fp G cs cur curi P rr _ v8); [clear MUL; close_vinv q' curi G cs curi G cs mi INV0| eexists; exact SCR| lia| lia| lia| exact MU0| exact WM0| exact PCH| exact PIN| exact K].
    - zstep. zstep. zstep. step.
      sgtB q' curi.
      destruct RES as [(tlz & ty & HR & -> & -> & -> & TL1 & -> & CL & TY5 & STRICT & CRB & CRL)|(HR & -> & ->)].
      + subst rr. step. lit_branch. zstep. rewrite (sx32_lit ty) by lia. zstep.
        joinB q'. pose proof (WL_out q' P 16 _ _ PIN MUL) as MUW.
        eapply (S_bodyV q' fp G cs cur curi tlz ty P v8); [clear MUL; close_vinv q' curi G cs (curi + tlz) G cs mi INV0| eexists; exact SCR| lia| lia| lia| lia| exact MU0| exact WM0| exact PCH
          | exact (shw_stepV q' _ _ P 16 SHP MUW)| exact PIN| unhide PAL; exact PAL| exact K|].
        intros. eapply (NEXT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tlz); eassumption.
      + joinB q'. pose proof (WL_out q' P 16 _ _ PIN MUL) as MUW.
        step. if_cases KB; zify_cond KB. { exfalso. lia. }
        eapply (S_exit_errV q' fp G cs cur curi P rr _ v8); [clear MUL; close_vinv q' curi G cs curi G cs mi INV0| eexists; exact SCR| lia| lia| lia| exact MU0| exact WM0| exact PCH| exact PIN| exact K].
  Qed.

  #[using="IC VOK RF0"] Lemma dir_SV : forall (q' fp G cs cur P : Z) (b2 : byte) (pw1 pw2 : word) x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    vinv q' cur G cs m ->
    acc m (fp + 1) -> ov_read_bytes asegs m (wa (fp + 1)) 1 = Some [b2] -> bv_unsigned b2 = 83 -> 0 <= fp < 2^62 ->
    rw_cells asegs m G [C8 (wz P)] -> shw m G 8 -> q <= G -> G + 8 <= 2^47 -> G mod 8 = 0 ->
    rw_cells asegs m P [C8 pw1; C8 pw2] -> shw m P 16 -> In (P, P + 16) Wx -> P mod 8 = 0 ->
    (forall (r cur' : Z) (pa pb : word) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m',
       vinv q' cur' (G + 8) cs m' -> munch (WP q' [(P, P + 16)]) m m' -> wmono asegs m m' -> 0 <= r <= 5 ->
       rw_cells asegs m' P [C8 pa; C8 pb] ->
       (r = 4 -> exists l, pa = wz (A + cur) /\ pb = wz l /\ 1 <= l /\ cur' = cur + l /\ cur' < len) ->
       evt asegs Q (contstA q' r (fp + 2) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m')) ->
    evt asegs Q (headstA q' fp 37 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m).
  Proof.
    intros q' fp G cs cur P b2 pw1 pw2 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m Q INV HACC RD HB FPR GC SHG GLO GHI GAL PC SHP PIN PAL K.
    eapply (pctV q' fp 83 G cs b2); [exact (proj1 (proj2 INV))| exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))) | reflexivity| exact HACC| exact RD| exact HB| exact FPR|].
    intros y1 y5 y6 y7 y13 y14 y15 y16 y17 y18 y27 y28 y29 y30 y31. cbn [vjt_off_A Z.eqb Pos.eqb Z.add].
    destruct (out_facts P 16 PIN ltac:(lia) ltac:(left; lia)) as (PLO & PHI & PPAR & PTXT).
    dir_intro q' INV. clear MUL MUP. pose proof (munch_refl ((lo, q' + 184) :: (S + 8, S + 16) :: (P, P + 16) :: Wx)%Z m) as MUL. pose proof (munch_refl ((lo, q' + 184) :: (S + 8, S + 16) :: [(P, P + 16)])%Z m) as MUP.
    pose proof (proj1 SHG) as ACG. load_anz.
    zstep. zstep. zstep. acc_chk0 11 G ACG. step. clear_shr. step. lit_branch. clear ACG. hide GAL.
    zstep. zstep. sstep.
    pose proof (proj1 (shw_stepV q' _ _ S 24 SHS (WL_out q' P 16 _ _ PIN MUL))) as ACS.
    acc_chk0 23 (S + 8) ACS. step. clear_shr. step. lit_branch.
    step. ubr. zstep. step. ubr.
    zstep. zstep. zstep.
    pose proof (proj1 (shw_stepV q' _ _ P 16 SHP (WL_out q' P 16 _ _ PIN MUL))) as ACP.
    acc_chk0 18 (P + 8) ACP. step. clear_shr. step. lit_branch. clear ACS ACP.
    zstep. zstep. sstep.
    pose proof (proj1 (shw_stepV q' _ _ S 24 SHS (WL_out q' P 16 _ _ PIN MUL))) as ACS.
    pose proof (proj1 (shw_stepV q' _ _ MB 32 SHMB (WL_out q' P 16 _ _ PIN MUL))) as ACM.
    zstep. zstep. pose proof S_al as SAL. acc_chk0 10 S ACS. clear SAL. step. clear_shr. step. lit_branch.
    pose proof MB_al as MBAL.
    zstep. step. ubr. zstep. step. ubr.
    zstep. zstep. acc_chk0 11 MB ACM. clear MBAL. step. clear_shr. step. lit_branch.
    zstep. sstep. zstep. step. ubr.
    zstep. zstep. zstep.
    replace (Z.lxor (Z.b2z (0 <? A)) (Z.b2z (cur + A <? 1))) with 1.
    2:{ destruct (Z.ltb_spec 0 A) as [AP|AN].
        - replace (cur + A <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
        - replace (cur + A <? 1) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
    step. lit_branch.
    pose proof (proj1 (shw_stepV q' _ _ P 16 SHP (WL_out q' P 16 _ _ PIN MUL))) as ACP.
    zstep. zstep. acc_chk0 12 P ACP. step. clear_shr. step. lit_branch.
    clear ACS ACM ACP. pose proof PAL as PAL'. hide PAL.
    sstep. sstep.
    replace (cur + A)%Z with (A + cur)%Z in * by lia.
    pose proof (WL_out q' P 16 _ _ PIN MUL) as MUW.
    eapply (S_loopV (Datatypes.S (Z.to_nat (len - cur))) 0x87418 q' fp (G + 8) cs cur cur P); [lia| left; reflexivity| clear MUL; close_vinv q' cur G cs cur (G + 8) cs m INV0| eexists; exact SCR| lia| exact MUP| exact WML
      | replace (cur - cur) with 0 by lia; exact PC| exact (shw_stepV q' _ _ P 16 SHP MUW)| exact PIN| exact PAL'| exact FPR| exact K].
  Qed.

  Definition vscrR (q' G cs : Z) (w0 w16 w32 : word) (m : mem) : Prop :=
    rw_cells asegs m q' [C8 w0; C8 (wz (Z.land (S + 16) 7 + 3)); C8 w16; C8 (wz (F + 32)); C8 w32; C8 (wz cur0); C8 (wz VMASK); C8 (wz F); C8 (wz F);
                         C8 (wz SF); C8 (wz SHE); C8 (wz (S + 16)); C8 (wz cs); C8 (wz (F + 64)); C8 (wz G); C8 (wz (S + 8)); C8 (wz F)].
  Definition XRv (cur r cur' : Z) (pa pb : word) : Prop :=
    r = 4 -> exists l, pa = wz (A + cur) /\ pb = wz l /\ 0 <= l /\ cur + l <= len /\ cur <= cur' /\ cur + l <= cur'.
  Definition KRt (q' : Z) (m : mem) (cur P fp G cs : Z) (Q : machine_state -> Prop) : Prop :=
    forall (r cur' : Z) (pa pb : word) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m',
       vinv q' cur' (G + 8) cs m' -> munch (WP q' [(P, P + 16)]) m m' -> wmono asegs m m' -> 0 <= r <= 5 ->
       rw_cells asegs m' P [C8 pa; C8 pb] -> XRv cur r cur' pa pb ->
       evt asegs Q (contstA q' r (fp + 2) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y25 y26 y27 y28 y29 y30 y31 m').
  Notation WLP q' P := ((lo, q' + 184) :: (S + 8, S + 16) :: (P, P + 16) :: Wx)%Z.

  #[using="VOK RF0"] Lemma R_failV : forall (q' fp G cs cur ci P rr : Z) (pa pb : word) x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x25 x26 x27 x28 x29 x30 x31 m mi (Q : machine_state -> Prop),
    vinv q' ci G cs mi -> cur0 <= cur <= len -> 0 <= rr <= 5 -> rr <> 4 ->
    munch (WP q' [(P, P + 16)]) m mi -> wmono asegs m mi ->
    rw_cells asegs mi P [C8 pa; C8 pb] -> In (P, P + 16) Wx ->
    KRt q' m cur P fp G cs Q ->
    evt asegs Q (MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') (wz rr) x11 x12 x13 x14 x15 x16 x17
                         (wz cur) (wz S) (wz 4) (wz 1) (wz 2147450880) (wz SHC) (wz (fp + 2)) x25 x26 x27 x28 x29 x30 x31)
                    F_ (wz 0x8719c) fc None mi (seg_rom asegs)).
  Proof.
    intros q' fp G cs cur ci P rr pa pb x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x25 x26 x27 x28 x29 x30 x31 m mi Q INV CI RR RN MU0 WM0 PCH PIN K.
    destruct (out_facts P 16 PIN ltac:(lia) ltac:(left; lia)) as (PLO & PHI & PPAR & PTXT).
    dir_intro q' INV. clear MUL MUP. pose proof (munch_refl (WLP q' P) mi) as MUL.
    pose proof (proj1 SHS) as ACS.
    acc_chk0 23 (S + 8) ACS. step. clear_shr. step. lit_branch. clear ACS.
    zstep. sstep. zstep. zstep. sstep. step.
    apply (WL_out q' P 16 _ _ PIN) in MUL.
    unfold contstA, vSHC in K. eapply (K rr cur); [| exact MU0| exact WM0| lia| exact PCH| intros X; exfalso; lia].
    close_vinv q' ci G cs cur (G + 8) cs mi INV0.
  Qed.

  #[using="VOK RF0"] Lemma R_okV : forall (q' fp G cs cur pos l P : Z) x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x25 x26 x27 x28 x29 x30 x31 m mi (Q : machine_state -> Prop),
    vinv q' pos G cs mi -> cur0 <= cur -> 0 <= l -> cur + l <= len -> cur <= pos <= len -> cur + l <= pos ->
    munch (WP q' [(P, P + 16)]) m mi -> wmono asegs m mi ->
    rw_cells asegs mi P [C8 (wz (A + cur)); C8 (wz l)] -> In (P, P + 16) Wx ->
    KRt q' m cur P fp G cs Q ->
    evt asegs Q (MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') (wz 4) x11 x12 x13 x14 x15 x16 x17
                         x18 (wz S) (wz 4) (wz 1) (wz 2147450880) (wz SHC) (wz (fp + 2)) x25 x26 x27 x28 x29 x30 x31)
                    F_ (wz 0x871ac) fc None mi (seg_rom asegs)).
  Proof.
    intros q' fp G cs cur pos l P x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x25 x26 x27 x28 x29 x30 x31 m mi Q INV C0 L0 CL PR LP MU0 WM0 PCH PIN K.
    destruct (out_facts P 16 PIN ltac:(lia) ltac:(left; lia)) as (PLO & PHI & PPAR & PTXT).
    dir_intro q' INV. clear MUL MUP. pose proof (munch_refl (WLP q' P) mi) as MUL.
    zstep. zstep. sstep. step.
    apply (WL_out q' P 16 _ _ PIN) in MUL.
    unfold contstA, vSHC in K. eapply (K 4 pos); [| exact MU0| exact WM0| lia| exact PCH|].
    - close_vinv q' pos G cs pos (G + 8) cs mi INV0.
    - intros _. exists l. repeat split; try reflexivity; lia.
  Qed.

  #[using="VOK RF0"] Lemma R_trimV : forall (k : nat) (q' fp G cs cur pos j P : Z) x1 x5 x6 x7 x11 x14 x15 x16 x17 x18 x26 x28 x29 x30 x31 m mi (Q : machine_state -> Prop),
    j < Z.of_nat k -> vinv q' pos G cs mi -> cur0 <= cur -> 0 <= j -> cur + j < len -> cur <= pos <= len -> cur + j + 1 <= pos + 2 ->
    (forall i, pos <= i <= cur + j -> exists b, nth_error bs (Z.to_nat i) = Some b /\ (bv_unsigned b = 13 \/ bv_unsigned b = 10)) ->
    munch (WP q' [(P, P + 16)]) m mi -> wmono asegs m mi ->
    rw_cells asegs mi P [C8 (wz (A + cur)); C8 (wz (j + 1))] -> shw mi P 16 -> In (P, P + 16) Wx -> P mod 8 = 0 ->
    KRt q' m cur P fp G cs Q ->
    evt asegs Q (MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') (wz 4) x11 (wz (A + cur)) (wz j) x14 x15 x16 x17
                         x18 (wz S) (wz 4) (wz 1) (wz 2147450880) (wz SHC) (wz (fp + 2)) (wz (P + 8)) x26 (wz (Z.shiftr (P + 8) 3 + 2147450880)) x28 x29 x30 x31)
                    F_ (wz 0x876f4) fc None mi (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros q' fp G cs cur pos j P x1 x5 x6 x7 x11 x14 x15 x16 x17 x18 x26 x28 x29 x30 x31 m mi Q HK INV C0 J0 JL PR JP CRF MU0 WM0 PCH SHP PIN PAL K; [lia|].
    destruct (out_facts P 16 PIN ltac:(lia) ltac:(left; lia)) as (PLO & PHI & PPAR & PTXT). pose proof PAL as PAL'. hide PAL.
    dir_intro q' INV. clear MUL MUP. pose proof (munch_refl (WLP q' P) mi) as MUL.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    destruct (nth_bsA (cur + j) ltac:(lia)) as [b Hb]. pose proof (byte_rangeA b) as BR.
    pose proof (proj1 (SHA ltac:(lia)) (A + cur + j) ltac:(lia)) as HACC.
    zstep. zstep. zstep.
    acc_chk 14 (A + cur + j) HACC k' SHR Hk.
    step.
    gen2 CONT 0x87708 14%nat 15%nat.
    2:{ destruct Hk as [-> | [K1 K2]].
        - step. lit_branch. apply CONT.
        - rewrite sxb_small by lia. step. if_cases KB; zify_cond KB. 2:{ exfalso; lia. }
          zstep. step. if_cases KC'; zify_cond KC'; zify_granule KC'; [apply CONT| exfalso; lia]. }
    intros ya4 ya5. clear SHR Hk HACC.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8ro_read asegs mm A bs (cur + j) b (Z_to_bv 64 (A + cur + j)) BUF Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
    zstep. cbn beta. zstep. step. if_cases K0; zify_cond K0.
    -
      assert (JP' : cur + (j + 1) <= pos).
      { destruct (Z_lt_le_dec (cur + j) pos) as [HL|HG]; [lia|]. exfalso. destruct (CRF (cur + j) ltac:(lia)) as (b' & Hb' & HV). rewrite Hb in Hb'. injection Hb' as <-. clear - HV K0. lia. }
      eapply (R_okV q' fp G cs cur pos (j + 1) P); [exact INV0| lia| lia| lia| lia| exact JP'| exact MU0| exact WM0| exact PCH| exact PIN| exact K].
    - zstep. zstep. zstep. step. if_cases K1; zify_cond K1.
      + assert (JP' : cur + (j + 1) <= pos).
        { destruct (Z_lt_le_dec (cur + j) pos) as [HL|HG]; [lia|]. exfalso. destruct (CRF (cur + j) ltac:(lia)) as (b' & Hb' & HV). rewrite Hb in Hb'. injection Hb' as <-.
          destruct HV as [HV|HV]; rewrite HV in K1; vm_compute in K1; first [discriminate K1| lia| (exfalso; apply K1; reflexivity)]. }
        eapply (R_okV q' fp G cs cur pos (j + 1) P); [exact INV0| lia| lia| lia| lia| exact JP'| exact MU0| exact WM0| exact PCH| exact PIN| exact K].
      + pose proof (proj1 SHP) as ACP.
        unhide PAL. acc_chk0 27 (P + 8) ACP. hide PAL. step. clear_shr. step. lit_branch. clear ACP.
        sstep. zstep. zstep.
        pose proof (WL_out q' P 16 _ _ PIN MUL) as MUW.
        assert (INV1 : vinv q' pos G cs _) by (clear MUL; close_vinv q' pos G cs pos G cs mi INV0).
        step. if_cases K2; zify_cond K2.
        *
          replace (j + -1) with (j - 1) by lia.
          eapply (IH q' fp G cs cur pos (j - 1) P); [lia| exact INV1| lia| lia| lia| lia| lia| intros i Hi; apply CRF; lia| exact MU0| exact WM0| | exact (shw_stepV q' _ _ P 16 SHP MUW)| exact PIN| exact PAL'| exact K].
          replace (j - 1 + 1) with j by lia. exact PCH.
        * step. eapply (R_okV q' fp G cs cur pos j P); [exact INV1| lia| lia| lia| lia| lia| exact MU0| exact WM0| exact PCH| exact PIN| exact K].
  Qed.

  #[using="VOK RF0"] Lemma R_doneV : forall (q' fp G cs cur ci pos l P : Z) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 x30 x31 m mi (Q : machine_state -> Prop),
    vinv q' ci G cs mi -> vscrR q' G cs (wz P) (wz cur) (wz (Z.shiftr P 3 + 2147450880)) mi ->
    cur0 <= cur -> 0 <= l -> cur + l <= len -> cur <= pos <= len -> cur + l <= pos + 2 ->
    (forall i, pos <= i < cur + l -> (exists b, nth_error bs (Z.to_nat i) = Some b /\ (bv_unsigned b = 13 \/ bv_unsigned b = 10))) ->
    munch (WP q' [(P, P + 16)]) m mi -> wmono asegs m mi ->
    rw_cells asegs mi P [C8 (wz (A + cur)); C8 (wz l)] -> shw mi P 16 -> In (P, P + 16) Wx -> P mod 8 = 0 ->
    KRt q' m cur P fp G cs Q ->
    evt asegs Q (MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') x10 x11 x12 x13 x14 x15 x16 x17
                         (wz pos) (wz S) (wz 4) (wz 1) (wz 2147450880) (wz SHC) (wz (fp + 2)) (wz (P + 8)) x26 (wz (Z.shiftr (P + 8) 3 + 2147450880)) x28 x29 x30 x31)
                    F_ (wz 0x876ac) fc None mi (seg_rom asegs)).
  Proof.
    intros q' fp G cs cur ci pos l P x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 x30 x31 m mi Q INV SCRW C0 L0 CL PR LP CRF MU0 WM0 PCH SHP PIN PAL K.
    destruct (out_facts P 16 PIN ltac:(lia) ltac:(left; lia)) as (PLO & PHI & PPAR & PTXT). pose proof PAL as PAL'.
    dir_intro q' INV. clear MUL MUP SCR. rename SCRW into SCR. unfold vscrR in SCR. pose proof (munch_refl (WLP q' P) mi) as MUL. load_anz.
    pose proof (proj1 SHS) as ACS.
    acc_chk0 23 (S + 8) ACS. step. clear_shr. step. lit_branch. clear ACS.
    zstep. sstep.
    pose proof (WL_out q' P 16 _ _ PIN MUL) as MUW.
    pose proof (shw_stepV q' _ _ P 16 SHP MUW) as SHP1. pose proof (proj1 SHP1) as ACP.
    acc_chk0 27 (P + 8) ACP. step. clear_shr. zstep. step. lit_branch.
    zstep. zstep.
    assert (INV1 : vinv q' pos G cs _) by (clear MUL; close_vinv q' ci G cs pos G cs mi INV0).
    step. if_cases K0; zify_cond K0.
    -
      eapply (R_okV q' fp G cs cur pos l P); [exact INV1| lia| lia| lia| lia| lia| exact MU0| exact WM0| exact PCH| exact PIN| exact K].
    - assert (APOS : 0 < A) by (apply ANZ; lia).
      zstep. acc_chk0 11 P ACP. step. clear_shr. step. lit_branch. clear ACP.
      zstep. step. ubr. zstep. step. ubr. zstep.
      replace (l + -1) with (l - 1) by lia.
      eapply (R_trimV (Datatypes.S (Z.to_nat l)) q' fp G cs cur pos (l - 1) P); [lia| exact INV1| lia| lia| lia| lia| lia| intros i Hi; apply CRF; lia| exact MU0| exact WM0| | exact SHP1| exact PIN| exact PAL'| exact K].
      replace (l - 1 + 1) with l by lia. exact PCH.
  Qed.

  Ltac shw_adv_with q' MUW WMW :=
    lazymatch type of MUW with munch _ ?ma ?mb =>
      repeat match goal with
      | H : asan_env asegs ma |- _ => apply (fun E => asan_env_frame asegs ma mb _ E MUW WMW (WL_env q')) in H
      | H : shw ma ?X ?n |- _ => apply (shw_stepV q' ma mb X n) in H; [| exact MUW]
      | H : shz ma _ _ |- _ => apply (shz_stepV q' ma mb) in H; [| exact MUW]
      | H : 0 < len -> shw ma A len |- _ =>
          let H' := fresh "SHA" in assert (H' : 0 < len -> shw mb A len) by (let HL := fresh in intros HL; exact (shw_stepV q' ma mb A len (H HL) MUW)); clear H
      end
    end.

  #[using="IC VOK RF0"] Lemma R_loopV : forall (k : nat) (q' fp G cs cur ci tlz ty saw pos P : Z) (tb : word) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m mi (Q : machine_state -> Prop),
    len - (ci + tlz) < Z.of_nat k -> cur0 <= cur <= ci -> 1 <= tlz -> ci + tlz <= len -> 0 <= ty <= 5 ->
    (saw = 0 \/ (saw = 1 /\ cur <= pos <= ci /\ ci <= pos + 2 /\ forall i, pos <= i < ci -> (exists b, nth_error bs (Z.to_nat i) = Some b /\ (bv_unsigned b = 13 \/ bv_unsigned b = 10)))) -> (ty = 2 -> tlz <= 2) ->
    (ty = 2 -> forall i, ci <= i < ci + tlz -> (exists b, nth_error bs (Z.to_nat i) = Some b /\ (bv_unsigned b = 13 \/ bv_unsigned b = 10))) ->
    vinv q' (ci + tlz) G cs mi -> vscrR q' G cs (wz P) (wz cur) (wz (Z.shiftr P 3 + 2147450880)) mi ->
    rw_cells asegs mi (q' + 164) [C4 (wz ty); C8 tb; C8 (wz tlz)] ->
    munch (WP q' [(P, P + 16)]) m mi -> wmono asegs m mi ->
    rw_cells asegs mi P [C8 (wz (A + cur)); C8 (wz (ci - cur))] -> shw mi P 16 -> In (P, P + 16) Wx -> P mod 8 = 0 -> 0 <= fp < 2^62 ->
    KRt q' m cur P fp G cs Q ->
    evt asegs Q (MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') x10 x11 x12 x13 x14 x15 x16 x17
                         (wz pos) (wz S) (wz 4) (wz 1) (wz 2147450880) (wz SHC) (wz (fp + 2)) (wz (P + 8)) (wz saw) (wz (Z.shiftr (P + 8) 3 + 2147450880)) x28 x29 x30 x31)
                    F_ (wz 0x87134) fc None mi (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros q' fp G cs cur ci tlz ty saw pos P tb x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m mi Q HK HCC TL1 HB TY5 SAW CRLX CRBX INV SCRW0 TKW0 MU0 WM0 PCH SHP PIN PAL FPR K; [lia|].
    destruct (out_facts P 16 PIN ltac:(lia) ltac:(left; lia)) as (PLO & PHI & PPAR & PTXT). pose proof PAL as PAL'. hide PAL.

    assert (CONT : forall (saw' pos' : Z) y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m',
      (saw' = 0 \/ (saw' = 1 /\ cur <= pos' <= ci + tlz /\ ci + tlz <= pos' + 2 /\ forall i, pos' <= i < ci + tlz -> (exists b, nth_error bs (Z.to_nat i) = Some b /\ (bv_unsigned b = 13 \/ bv_unsigned b = 10)))) ->
      vinv q' (ci + tlz) G cs m' -> vscrR q' G cs (wz P) (wz cur) (wz (Z.shiftr P 3 + 2147450880)) m' ->
      rw_cells asegs m' (q' + 164) [C4 (wz ty); C8 tb; C8 (wz tlz)] ->
      munch (WP q' [(P, P + 16)]) m m' -> wmono asegs m m' ->
      rw_cells asegs m' P [C8 (wz (A + cur)); C8 (wz (ci - cur))] -> shw m' P 16 ->
      evt asegs Q (MS (mkR y1 (wz q') gp tp y5 y6 y7 (wz q) (wz q') y10 y11 y12 y13 y14 y15 y16 y17
                         (wz pos') (wz S) (wz 4) (wz 1) (wz 2147450880) (wz SHC) (wz (fp + 2)) (wz (P + 8)) (wz saw') (wz (Z.shiftr (P + 8) 3 + 2147450880)) y28 y29 y30 y31)
                    F_ (wz 0x8716c) fc None m' (seg_rom asegs))).
    { intros until m'. intros SAW' INV' SCRW' TKW' MU' WM' PCH' SHP'.
      pose proof SCRW' as SCRW. unfold vscrR in SCRW.
      dir_intro q' INV'. clear MUL MUP SCR. rename SCRW into SCR. pose proof TKW' as TKW. pose proof (munch_refl (WLP q' P) m') as MUL.
      pose proof (proj1 SHP') as ACP.
      unhide PAL. acc_chk0 27 (P + 8) ACP. hide PAL. step. clear_shr. step. lit_branch. clear ACP.
      zstep. zstep. zstep. sstep.
      replace (ci - cur + tlz) with (ci + tlz - cur) in * by lia.
      clear TKW. pose proof SHP' as SHP0. hide SHP0.
      pose proof (WL_out q' P 16 _ _ PIN MUL) as MUW0. shw_adv_with q' MUW0 WML. clear MUW0.
      zstep. zstep. zstep. step.
      sgtB q' (ci + tlz).
      destruct RES as [(tlz2 & ty2 & HR & -> & -> & -> & TL2 & -> & CL2 & TY52 & STRICT2 & CRB2 & CRL2)|(HR & -> & ->)].
      - subst rr. step. lit_branch.
        pose proof TYB as TYB'. pose proof TKB as TKB'. join_chunks TYB' TKB' TKW2.
        joinB q'. pose proof (WL_out q' P 16 _ _ PIN MUL) as MUW.
        eapply (IH q' fp G cs cur (ci + tlz) tlz2 ty2 saw' pos' P _); [lia| lia| lia| lia| lia| exact SAW'| exact CRL2| exact CRB2
          | clear MUL; close_vinv q' (ci + tlz) G cs (ci + tlz + tlz2) G cs m' INV0| exact SCR| exact TKW2| exact MU'| exact WM'| exact PCH'
          | exact (shw_stepV q' _ _ P 16 SHP0 MUW)| exact PIN| exact PAL'| exact FPR| exact K].
      - joinB q'. pose proof (WL_out q' P 16 _ _ PIN MUL) as MUW.
        step. if_cases KB; zify_cond KB. { exfalso. lia. }
        zstep.
        eapply (R_failV q' fp G cs cur (ci + tlz) P rr); [clear MUL; close_vinv q' (ci + tlz) G cs (ci + tlz) G cs m' INV0| lia| lia| lia| exact MU'| exact WM'| exact PCH'| exact PIN| exact K]. }
    clear IH.
    pose proof SCRW0 as SCRW. unfold vscrR in SCRW.
    pose proof INV as INVk.
    dir_intro q' INV. clear MUL MUP SCR. rename SCRW into SCR. pose proof TKW0 as TKW.
    zstep. rewrite (sx32_lit ty) by lia.
    step. if_cases K1; zify_cond K1.
    -
      step. if_cases K2; zify_cond K2.
      +
        eapply (R_doneV q' fp G cs cur (ci + tlz) pos (ci - cur) P); [exact INVk| exact SCRW0| lia| lia| lia| lia| lia
          | destruct SAW as [S0|(_ & _ & _ & SCR1)]; [exfalso; lia| intros i Hi; apply SCR1; lia]
          | exact MU0| exact WM0| exact PCH| exact SHP| exact PIN| exact PAL'| exact K].
      + zstep. eapply (CONT 0 pos); [left; reflexivity| exact INVk| exact SCRW0| exact TKW0| exact MU0| exact WM0| exact PCH| exact SHP].
    -
      zstep. step. if_cases K2; zify_cond K2.
      + zstep. eapply (CONT 0 pos); [left; reflexivity| exact INVk| exact SCRW0| exact TKW0| exact MU0| exact WM0| exact PCH| exact SHP].
      +
        pose proof (proj1 SHS) as ACS.
        acc_chk0 23 (S + 8) ACS. step. clear_shr. step. lit_branch. clear ACS.
        zstep. zstep. zstep. zstep. zstep. step.
        replace (ci + tlz - tlz) with ci by lia.
        eapply (CONT 1 ci); [right; split; [reflexivity|]; split; [lia|]; split; [specialize (CRLX ltac:(lia)); lia| exact (CRBX ltac:(lia))]| exact INVk| exact SCRW0| exact TKW0| exact MU0| exact WM0| exact PCH| exact SHP].
  Qed.

  #[using="IC VOK RF0"] Lemma dir_RV : forall (q' fp G cs cur P : Z) (b2 : byte) (pw1 pw2 : word) x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    vinv q' cur G cs m ->
    acc m (fp + 1) -> ov_read_bytes asegs m (wa (fp + 1)) 1 = Some [b2] -> bv_unsigned b2 = 82 -> 0 <= fp < 2^62 ->
    rw_cells asegs m G [C8 (wz P)] -> shw m G 8 -> q <= G -> G + 8 <= 2^47 -> G mod 8 = 0 ->
    rw_cells asegs m P [C8 pw1; C8 pw2] -> shw m P 16 -> In (P, P + 16) Wx -> P mod 8 = 0 ->
    KRt q' m cur P fp G cs Q ->
    evt asegs Q (headstA q' fp 37 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m).
  Proof.
    intros q' fp G cs cur P b2 pw1 pw2 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x26 x27 x28 x29 x30 x31 m Q INV HACC RD HB FPR GC SHG GLO GHI GAL PCH SHP PIN PAL K.
    eapply (pctV q' fp 82 G cs b2); [exact (proj1 (proj2 INV))| exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))) | reflexivity| exact HACC| exact RD| exact HB| exact FPR|].
    intros y1 y5 y6 y7 y13 y14 y15 y16 y17 y18 y27 y28 y29 y30 y31. cbn [vjt_off_A Z.eqb Pos.eqb Z.add].
    destruct (out_facts P 16 PIN ltac:(lia) ltac:(left; lia)) as (PLO & PHI & PPAR & PTXT).
    dir_intro q' INV. clear MUL MUP. pose proof (munch_refl (WLP q' P) m) as MUL. pose proof (munch_refl ((lo, q' + 184) :: (S + 8, S + 16) :: [(P, P + 16)])%Z m) as MUP.
    pose proof (proj1 SHS) as ACS. pose proof (proj1 SHMB) as ACM. pose proof (proj1 SHP) as ACP. pose proof (proj1 SHG) as ACG. load_anz.
    zstep. zstep. zstep. acc_chk0 11 G ACG. step. clear_shr. step. lit_branch.
    acc_chk0 23 (S + 8) ACS. step. clear_shr. step. lit_branch.
    zstep. zstep. pose proof S_al as SAL. acc_chk0 10 S ACS. clear SAL. step. clear_shr. step. lit_branch.
    pose proof MB_al as MBAL.
    zstep. step. ubr. zstep. step. ubr.
    zstep. zstep. acc_chk0 11 MB ACM. clear MBAL. step. clear_shr. step. lit_branch.
    zstep. zstep. zstep. step. ubr.
    zstep. zstep. zstep.
    replace (Z.lxor (Z.b2z (0 <? A)) (Z.b2z (cur + A <? 1))) with 1.
    2:{ destruct (Z.ltb_spec 0 A) as [AP|AN].
        - replace (cur + A <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
        - replace (cur + A <? 1) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
    step. lit_branch.
    zstep. zstep. step. ubr. zstep. step. ubr.
    zstep. zstep. acc_chk0 12 P ACP. step. clear_shr. step. lit_branch.
    clear ACS ACM ACP ACG. pose proof PAL as PAL'. hide PAL. hide GAL.
    sstep. sstep. zstep. zstep. zstep.
    replace (cur + A)%Z with (A + cur)%Z in * by lia.
    pose proof (proj1 (shw_stepV q' _ _ P 16 SHP (WL_out q' P 16 _ _ PIN MUL))) as ACP.
    unhide PAL. acc_chk0 27 (P + 8) ACP. hide PAL. step. clear_shr. step. lit_branch. clear ACP.
    sstep.
    pose proof SHP as SHP0. hide SHP0.
    pose proof (WL_out q' P 16 _ _ PIN MUL) as MUW0. shw_adv_with q' MUW0 WML. clear MUW0.
    zstep. zstep. zstep. step.
    sgtB q' cur.
    destruct RES as [(tlz & ty & HR & -> & -> & -> & TL1 & -> & CL & TY5 & STRICT & CRB & CRL)|(HR & -> & ->)].
    - subst rr. step. lit_branch.
      sstep. sstep. zstep. zstep.
      pose proof TYB as TYB'. pose proof TKB as TKB'. join_chunks TYB' TKB' TKW2.
      joinB q'. pose proof (WL_out q' P 16 _ _ PIN MUL) as MUW.
      eapply (R_loopV (Datatypes.S (Z.to_nat (len - cur))) q' fp G cs cur cur tlz ty 0 0 P _); [lia| lia| lia| lia| lia| left; reflexivity| exact CRL| exact CRB
        | clear MUL; close_vinv q' cur G cs (cur + tlz) G cs m INV0| exact SCR| exact TKW2| exact MUP| exact WML
        | replace (cur - cur) with 0 by lia; exact PCH| exact (shw_stepV q' _ _ P 16 SHP0 MUW)| exact PIN| exact PAL'| exact FPR| exact K].
    - joinB q'. pose proof (WL_out q' P 16 _ _ PIN MUL) as MUW.
      step. if_cases KB; zify_cond KB. 2:{ exfalso. lia. }
      eapply (R_failV q' fp G cs cur cur P rr); [clear MUL; close_vinv q' cur G cs cur G cs m INV0| lia| lia| lia| exact MUP| exact WML| exact PCH| exact PIN| exact K].
  Qed.

  Definition vpostA (X : mem -> Z -> Z -> Prop) : machine_state -> Prop :=
    fun ms' => exists (r cur' : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (st' : fsstate FI),
      ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch W0 m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
      /\ fkeep FI WV st m0 m' /\ fs_live FI st' = fs_live FI st /\ RFAKE FI st' m'
      /\ stk asegs m' lo q /\ asan_env asegs m'
      /\ rw_cells asegs m' S [C8 (wz MB); C8 (wz cur'); C4 (wz 0)] /\ rw_cells asegs m' MB (mbuf_cells A len cap) /\ bytes_at asegs m' A bs
      /\ shz m' (sh lo) (sh q)
      /\ 0 <= r <= 5 /\ 0 <= cur' <= len /\ (r = 4 -> cur0 <= cur') /\ (r <> 4 -> cur' = cur0)
      /\ X m' r cur'.

  Definition vWE : list ivl := [(lo, q); (F, F + 128); (SF, SF + 16); (FL, FL + 1); (S + 8, S + 16)]%Z.
  Definition rframeA (R : mem -> Prop) : Prop := forall m m', R m -> munch vWE m m' -> wmono asegs m m' -> R m'.

  #[using="VOK RF0"] Lemma epiV : forall (q' r cur' G cs : Z) (R : mem -> Prop) (XP : Z -> Z -> Prop)
      x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m,
    vinv q' cur' G cs m -> 0 <= r <= 5 -> (r = 4 -> cur0 <= cur') -> (r <> 4 -> cur' = cur0) ->
    R m -> rframeA R -> XP r cur' ->
    evt asegs (vpostA (fun m' r c => R m' /\ XP r c))
      (epistA q' r x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m).
  Proof.
    intros q' r cur' G cs R XP x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m INV RR ROK RNOK HR RFR HXP.
    unfold epistA.
    open_vinv INV.
    destruct VR as (Hq & GAP & FRhi & FH & (e & j & FT1) & FT2 & SHF & FLG & MU & WM & FK & RF & LIVE1).
    pose proof VOK as VOK'; destruct VOK' as (CLO & LO & _ & QHI & MBLO & MBS & SHI & _ & _ & PLB & A0 & AHI & LBS & CAP & ACAP & CUR0 & TXP & _ & _ & _ & _ & _).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR. unfold vSHC, vSHE in *.
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & _ & FSB4 & FSB5).
    destruct (new_frame_facts FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & FLO & FHI & FAL & FLLO & FLHI & APART).
    cbn [FB_of SB_of] in FHI, APART.
    assert (SFB : 8 * (SF - 2147450880) = F) by (unfold vSF, sh, SHADOW_OFF; clear - FAL; Z.div_mod_to_equations; lia).
    assert (SHB8 : 8 * (sh (FSB FI) - 2147450880) = FSB FI) by (unfold sh, SHADOW_OFF; clear - FSB4; Z.div_mod_to_equations; lia).
    hide FAL. hide FSB4. hide Hq. hide TXP. hide BUF.
    pose proof (new_frame_fk FI st 1 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
    assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI st1)) by (intros g Hg; rewrite LIVE1; right; exact Hg).
    pose proof (lb_new _ _ _ LIVE1) as LVF. pose proof (ls_new _ _ _ LIVE1) as LVS. pose proof (lf_new _ _ _ LIVE1) as LVL.
    unfold ff_size, ff_shsize in LVF, LVS. rewrite FCLS in LVF, LVS. cbn [FB_of SB_of] in LVF, LVS.
    change (ff_addr (fs_newff FI st 1)) with F in LVF, LVS. change (ff_flag (fs_newff FI st 1)) with FL in LVL. change (sh F) with SF in LVS.
    destruct (lb_in_fs _ _ PLB) as [PB1 PB2]. pose proof (lb_apart_frame _ _ _ F 128 _ _ PLB APART) as PF. clear APART PLB.
    pose proof (munch_refl vWE m) as MUE. pose proof (wmono_refl asegs m) as WME. unfold vWE in MUE.
    pose proof (munch_refl [(lo, q); (F, F + 128); (SF, SF + 16)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
    zstep. zstep.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(SF, SF + 16)]%Z mm) as MUs; pose proof (wmono_refl asegs mm) as WMs end.
    hide_mem_except SHF. unhide MUs. unhide WMs.
    sstep. sstep.
    unhide_transport MUs WMs. clear MUs WMs.
    zstep. zstep. zstep. sstep.
    zstep.
    step. if_cases K0; zify_cond K0. { exfalso. lia. } clear K0.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(SF, SF + 16)]%Z mm) as MUs; pose proof (wmono_refl asegs mm) as WMs end.
    hide_mem_except SHF. unhide MUs. unhide WMs.
    do 16 sstep.
    unhide_transport MUs WMs. clear MUs WMs.
    zstep.

    env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(FL, FL + 1)]%Z mm) as MU0; pose proof (wmono_refl asegs mm) as WM0 end.
    sstep.
    env_sync AE MU0 WM0. fk_sync FI RF MU0 FK LSUB.
    join_chunks FT1 FT2 FRt. join_chunks FH FRt FRF.
    lazymatch type of RF with RFAKE _ ?st2 ?mb =>
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (SHF' : rw_cells asegs mc (sh (ff_addr (fs_newff FI st 1))) (shadow_cells (repeat 245 (Z.to_nat (ff_shsize (fs_newff FI st 1))))))
        by (change (ff_addr (fs_newff FI st 1)) with F; change (sh F) with SF; unfold ff_shsize; rewrite FCLS; exact SHF);
      destruct (release FI st2 (fs_newff FI st 1) (fs_live FI st) mb mc _ RF LIVE1 MU0 WM0 FLG SHF' FRF
                  ltac:(unfold ff_size; rewrite FCLS; reflexivity)) as [RF3 LIVE3]
    end end.
    clear RF MU0 WM0 SHF'.
    step.   zstep.
    do 13 step.
    step.   step.
    release_frame SCR ST (q' + 136)%Z. release_frame TOK ST (q' + 184)%Z.
    pose proof (stk_merge asegs _ _ _ _ ST GAP ltac:(lia)) as STm. clear ST GAP.
    release_frame FRhi STm q.

    pose proof VOK as VOK'; destruct VOK' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TFS & TBAND & _ & WXT & _).
    assert (WEF : Forall (fsw_iv FI) [(lo, q); (F, F + 128); (SF, SF + 16); (FL, FL + 1); (S + 8, S + 16)]%Z).
    { apply fsw_cons_app; [apply app_iv_stack; lia|]. apply fsw_cons_app; [apply sub_app_iv_fs; lia|].
      constructor; [right; cbn [fst snd]; lia|]. apply fsw_cons_app; [apply sub_app_iv_fs; lia|]. apply fsw_cons_app; [apply sub_app_iv_fs; lia| constructor]. }
    pose proof (shz_stack_fs FI _ m _ lo _ _ SHZ CLO (stack_lo_ok lo) (sh_hi_ok q QHI) MUE WEF) as SHZ'.
    unhide BUF. unhide TXP.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (BUF' : bytes_at asegs mm A bs) end.
    { apply (bytes_at_transport asegs _ m _ A bs BUF MUE). cbn [disjoint_from].
      split; [lia|]. split; [clear - TFS FLO FHI; lia|]. split; [clear - TBAND SFB SHB8 FLO FHI FSB1 FSB2 ACR; lia|]. split; [clear - TFS FLLO FLHI; lia|]. split; [clear - TXP MBS; lia| exact I]. }
    apply evt_done. unfold vpostA. exists r, cur'. do 14 eexists. lazymatch goal with |- exists _ _, MS _ _ _ _ _ ?mm _ = _ /\ _ => exists mm, (fs_after_release FI st1) end.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FK|]. split; [exact LIVE3|]. split; [exact RF3|].
    split; [exact STm|]. split; [exact AE|]. split; [exact SC|]. split; [unfold mbuf_cells, MEMBUF_DEF_SIZE_INC; exact MBC|]. split; [exact BUF'|]. split; [exact SHZ'|].
    split; [exact RR|]. split; [lia|]. split; [exact ROK|]. split; [exact RNOK|]. split; [exact (RFR m _ HR MUE WME)| exact HXP].
  Qed.

  #[using="VOK RF0"] Lemma errV : forall (q' r cur' G cs : Z) (R : mem -> Prop) (XP : Z -> Z -> Prop)
      x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 m,
    vinv q' cur' G cs m -> 0 <= r <= 5 -> r <> 4 -> R m -> rframeA R -> XP r cur0 ->
    evt asegs (vpostA (fun m' r c => R m' /\ XP r c))
      (errstA q' r x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 m).
  Proof.
    intros q' r cur' G cs R XP x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 m INV RR RN HR RFR HXP.
    unfold errstA. dir_intro q' INV. unfold vWL in MUL.
    pose proof (munch_refl vWE m) as MUE. pose proof (wmono_refl asegs m) as WME. unfold vWE in MUE.
    zstep. step. if_cases KR4; zify_cond KR4. { exfalso. lia. } clear KR4.
    pose proof (proj1 SHS) as ACS.
    acc_chk0 23 (S + 8) ACS. step. clear_shr. step. lit_branch. clear ACS.
    zstep. zstep. sstep.
    eapply (epiV q' r cur0 G cs R XP); [close_vinv q' cur' G cs cur0 G cs m INV0| exact RR| intros X; exfalso; lia| intros _; reflexivity| exact (RFR m _ HR MUE WME)| exact RFR| exact HXP].
  Qed.

End VF.
End W.
