(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MALLOC_ENTRY : Z := 0x56178.   (* [comment removed for export] *)
Definition CALLOC_ENTRY : Z := 0x5617c.   (* [comment removed for export] *)
Definition REALLOC_ENTRY : Z := 0x56180.  (* [comment removed for export] *)
Definition FREE_ENTRY : Z := 0x56174.     (* [comment removed for export] *)
Definition FOPEN_ENTRY : Z := 0x444d4.    (* [comment removed for export] *)
Definition FCLOSE_ENTRY : Z := 0x444dc.
Definition FREAD_ENTRY : Z := 0x4448c.
Definition VSNPRINTF_ENTRY : Z := 0x444a4.
Definition SNPRINTF_ENTRY : Z := 0x444b0.
Definition STRERROR_R_ENTRY : Z := 0x444c4.
Definition STRLEN_ENTRY : Z := 0x44468.
Definition FPRINTF_ENTRY : Z := 0x444ac.
Definition PRINTF_ENTRY : Z := 0x444a8.
Definition FWRITE_ENTRY : Z := 0x44490.
Definition MEMCPY_ENTRY : Z := 0x54964.   (* [comment removed for export] *)
Definition MEMSET_ENTRY : Z := 0x54e00.   (* [comment removed for export] *)
Definition FERROR_ENTRY : Z := 0x9a2cc.   (* [comment removed for export] *)
Definition FILENO_ENTRY : Z := 0x9a758.
Definition ERRNO_LOCATION_ENTRY : Z := 0x944b8.
Definition REMOVE_ENTRY : Z := 0x9ad50.
Definition UNLINK_ENTRY : Z := 0xa3edc.
Definition CLOSE_ENTRY : Z := 0xa3dc8.
Definition MKSTEMP_ENTRY : Z := 0x8dcc4.  (* [comment removed for export] *)
Definition STACK_MALLOC_0 : Z := 0x3f278. (* [comment removed for export] *)
Definition STACK_MALLOC_1 : Z := 0x3f3ec. (* [comment removed for export] *)
Definition STACK_MALLOC_7 : Z := 0x3f57c. (* [comment removed for export] *)
Definition STACK_FREE_7 : Z := 0x3f6f8.   (* [comment removed for export] *)
Definition SET_SHADOW_00 : Z := 0x58268.  (* [comment removed for export] *)
Definition SET_SHADOW_F8 : Z := 0x58388.
Definition STDIN_FILE : Z := 0xa9ba0.     (* [comment removed for export] *)
Definition STDIN_P : Z := 0xa53a8.        (* [comment removed for export] *)
Definition GOT_STDIN : Z := 0xa6158.      (* [comment removed for export] *)
Definition GOT_SHBASE : Z := 0xa54b0.     (* [comment removed for export] *)
Definition GOT_MEMSET : Z := 0xa54d0.     (* [comment removed for export] *)
Definition GOT_UAR : Z := 0xa5508.        (* [comment removed for export] *)
Definition STR_RB : Z := 0x212e0.         (* [comment removed for export] *)
Definition STR_PERCENT_S : Z := 0x21300.  (* [comment removed for export] *)
Definition STR_PERCENT_S_FMT : Z := 0x217a0. (* [comment removed for export] *)
Definition STR_STATS_NA : Z := 0x215a0.   (* [comment removed for export] *)
Definition STR_MALLOC : Z := 0x21640.     (* [comment removed for export] *)

Definition OUTFILE_ADDR : Z := 0x5e0c80.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition MALLOC_STACK : Z := 4096.
Definition REALLOC_STACK : Z := 8192.     (* [comment removed for export] *)
Definition FREE_STACK : Z := 4096.
Definition FAKE_STACK : Z := 4096.        (* [comment removed for export] *)
Definition STDIO_STACK : Z := 0x4000.
Definition PCAP_L0_STACK : Z := 0x6000.   (* [comment removed for export] *)
Definition PCAP_L1_STACK : Z := 0x8000.   (* [comment removed for export] *)
Definition PCAP_L1B_STACK : Z := 0xa000.  (* [comment removed for export] *)
Definition PCAP_L2_STACK : Z := 0xe000.   (* [comment removed for export] *)
Definition PCAP_L3_STACK : Z := 0x10000.  (* [comment removed for export] *)
Definition PCAP_L4_STACK : Z := 0x12000.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition open_name_ok (wr : bool) (name : list byte) : Prop :=
  if wr then (Namei.path_has_slash name = false \/ name = Uapi.devnull_path)
  else (Namei.path_has_slash name = false /\ Fs.path_eqb name Namei.dotdot_path = false).

(* [comment removed for export] *)
Notation rng_aimg_sh RNG := (rng RNG 0x7fffa000 779776).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ff_class (f : fframe) : Z :=
  match f with
  | FF_FOPEN_OFFLINE | FF_FMT_ERRMSG | FF_NG_CHECK_HEADER | FF_READ_BLOCK => 0
  | FF_CHECK_HEADER | FF_OFFLINE_READ | FF_NEXT_EX => 1
  | FF_NEXT_PACKET | FF_FUZZ_ONE_INPUT => 7
  end.
Definition ff_size (f : fframe) : Z := 64 * 2 ^ ff_class f.
(* [comment removed for export] *)
Definition site_frameA (site : stack_site) : option (fframe * Z) :=
  match site with
  | SiteMagic => Some (FF_FOPEN_OFFLINE, 32)
  | SitePcapHdrRest => Some (FF_CHECK_HEADER, 36)
  | SiteSfHdr => Some (FF_NEXT_PACKET, 32)
  | SiteDiscardBuf => Some (FF_NEXT_PACKET, 96)
  | SiteNgTotalLength => Some (FF_NG_CHECK_HEADER, 32)
  | SiteNgByteOrderMagic => Some (FF_NG_CHECK_HEADER, 48)
  | SiteBhdrCheckHeader | SiteBhdrNextPacket => Some (FF_READ_BLOCK, 32)
  | SiteReadStage => None
  end.

Section Ifaces.
  Context {rc : runConstT} {tlsI : ABase.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  #[local] Abbreviation MP := (Monad.M (PState H hptr)).
  #[local] Abbreviation pcapT := (PcapTypes.pcap hptr hptr).
  #[local] Abbreviation PR := (prims HO FO sites).
  #[local] Abbreviation PCR := (@PCAPR hptr).
  #[local] Abbreviation PCRC := (@PCAPR_closable hptr).

  (* [comment removed for export] *)
  Variable GIOA : alayout -> footprint -> PS -> list cblk -> list cblk -> list fblock -> mem -> Prop.
  (* [comment removed for export] *)
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation GIO := GIOA.

  (* [comment removed for export] *)
  Definition iv_in_frames (FL : list fblock) (iv : Z * Z) : Prop :=
    Exists (fun fr => fb_addr fr <= fst iv /\ snd iv <= fb_addr fr + fb_size fr) FL.
  Definition iv_in_frame_shadow (FL : list fblock) (iv : Z * Z) : Prop :=
    Exists (fun fr => Z.shiftr (fb_addr fr) 3 + 2147450880 <= fst iv /\ snd iv <= Z.shiftr (fb_addr fr) 3 + 2147450880 + Z.shiftr (fb_size fr) 3) FL.
  Definition client_ivA (FL : list fblock) (CL : list cblk) (iv : Z * Z) : Prop :=
    ATOP + 4096 <= fst iv \/ iv_in_block CL iv \/ iv_in_frames FL iv \/ iv_in_frame_shadow FL iv.
  Definition pcap_iv (FL : list fblock) (PB : list cblk) (iv : Z * Z) : Prop := client_ivA FL PB iv.

  Record gia_laws : Prop := mkGL {
    (* [comment removed for export] *)
    gl_block : forall L RNG s CL FB FL m b, GIOA L RNG s CL FB FL m -> In b (CL ++ FB) -> blockA RNG m b;
    gl_apart : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m -> blocks_apart (CL ++ FB);
    (* [comment removed for export] *)
    gl_frames : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m -> Forall (frameA RNG m) FL /\ List.NoDup (map fb_fn FL);
    gl_fr_apart : forall L RNG s CL FB FL m a, GIOA L RNG s CL FB FL m -> in_frames FL a -> ~ in_block (CL ++ FB) a;
    gl_fr_disj : forall L RNG s CL FB FL m fr1 fr2, GIOA L RNG s CL FB FL m -> In fr1 FL -> In fr2 FL -> fb_fn fr1 <> fb_fn fr2 ->
                 fb_addr fr1 + fb_size fr1 <= fb_addr fr2 \/ fb_addr fr2 + fb_size fr2 <= fb_addr fr1;
    gl_site : forall L RNG s CL FB FL m f Fb n site off, GIOA L RNG s CL FB FL m -> In (f, Fb, n) FL ->
                 site_frameA site = Some (f, off) -> fo_site FO s site = Some (Fb + off);
    gl_flag : forall L RNG s CL FB FL m f Fb n, GIOA L RNG s CL FB FL m -> In (f, Fb, n) FL ->
                 rw_cells asegs m (fflagA L f Fb) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflagA L f Fb) 1
                 /\ ablk (fflagA L f Fb) (fflagA L f Fb + 1) /\ fflagA L f Fb + 1 <= ATOP
                 /\ ~ in_block (CL ++ FB) (fflagA L f Fb) /\ ~ in_frames FL (fflagA L f Fb);
    (* [comment removed for export] *)
    gl_client_frame : forall L RNG s CL FB FL m m' W, GIOA L RNG s CL FB FL m -> munch W m m' -> wmono asegs m m' ->
                 Forall (client_ivA FL CL) W -> GIOA L RNG s CL FB FL m';
    gl_frame : forall L RNG s CLc PB FB FL m m' W, GIOA L RNG s (CLc ++ PB) FB FL m -> munch W m m' -> wmono asegs m m' ->
                 Forall (pcap_iv FL PB) W -> GIOA L RNG s (CLc ++ PB) FB FL m';
    gl_keeps : forall L RNG s CLc PB FB FLc FLo m m' W SP, GIOA L RNG s (CLc ++ PB) FB (FLo ++ FLc) m -> munch W m m' -> wmono asegs m m' ->
                 Forall (fun iv => (ATOP + 4096 <= fst iv /\ snd iv <= SP) \/ iv_in_block PB iv \/ iv_in_frames FLo iv \/ iv_in_frame_shadow FLo iv) W ->
                 ATOP + 4096 <= SP -> agrees_on (client_keeps FLc CLc SP) m m';
    (* [comment removed for export] *)
    gl_keepsx : forall L RNG s CLc PB FB FLc FLo m m' W WX SP, GIOA L RNG s (CLc ++ PB) FB (FLo ++ FLc) m -> munch (W ++ WX) m m' -> wmono asegs m m' ->
                 Forall (fun iv => (ATOP + 4096 <= fst iv /\ snd iv <= SP) \/ iv_in_block PB iv \/ iv_in_frames FLo iv \/ iv_in_frame_shadow FLo iv) W ->
                 ATOP + 4096 <= SP -> agrees_on (fun a => client_keeps FLc CLc SP a /\ outside WX a) m m';
    (* [comment removed for export] *)
    gl_rt : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m ->
                 artcells m /\ rw_cells asegs m GOT_UAR [C8 (Z_to_bv 64 0xae600)];
    (* [comment removed for export] *)
    gl_globals : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m ->
                 wr_at asegs m 0x7fffa000 779776 /\ Forall (fun g => unpoisoned m (fst g) (fst g + snd g)) client_globals;
    (* [comment removed for export] *)
    gl_tls : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m -> rng_atls RNG -> mobjA RNG m (ATP + -200) 504;
    (* [comment removed for export] *)
    gl_tls_apart : forall L RNG s CL FB FL m a, GIOA L RNG s CL FB FL m -> in_block (CL ++ FB) a \/ in_frames FL a ->
                 ~ (ATP + -200 <= a < ATP + -200 + 504);
    (* [comment removed for export] *)
    gl_stdin : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m ->
                 rw_cells asegs m GOT_STDIN [C8 (Z_to_bv 64 STDIN_P)] /\ rw_cells asegs m STDIN_P [C8 (Z_to_bv 64 STDIN_FILE)]
                 /\ unpoisoned m STDIN_P (STDIN_P + 8);
    (* [comment removed for export] *)
    gl_stack : forall L RNG s CL FB FL m A n, GIOA L RNG s CL FB FL m -> ATOP + 4096 <= A -> 0 <= n -> A + n <= al_top L ->
                 unpoisoned m A (A + n) /\ arenaA RNG m A n;
    (* [comment removed for export] *)
    gl_got_memset : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m -> rw_cells asegs m GOT_MEMSET [C8 (Z_to_bv 64 0xa7360)]
  }.

  (* [comment removed for export] *)
  Definition gia_addr_law : Prop :=
    forall L RNG s CL FB FL m b, GIOA L RNG s CL FB FL m -> In b (CL ++ FB) -> blk_addr HO s (cb_tok b) = cb_addr b.
  (* [comment removed for export] *)
  Definition gia_perm_law : Prop :=
    forall L RNG s CL CL' FB FL m, GIOA L RNG s CL FB FL m -> Permutation.Permutation CL CL' -> GIOA L RNG s CL' FB FL m.
  (* [comment removed for export] *)
  Record gia_harn_laws : Prop := mkGH {
    gh_outfile : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m ->
                 match ps_outfile s with
                 | None => rw_cells asegs m OUTFILE_ADDR [C8 (Z_to_bv 64 0)]
                 | Some q => exists A, In (q, A, FILE_BLOCK) FB /\ rw_cells asegs m OUTFILE_ADDR [C8 (Z_to_bv 64 A)]
                 end;
    (* [comment removed for export] *)
    gh_set_outfile : forall L RNG s CL FB FL m m' (o : option hptr), GIOA L RNG s CL FB FL m -> ps_outfile s = None ->
                 match o with
                 | None => rw_cells asegs m' OUTFILE_ADDR [C8 (Z_to_bv 64 0)]
                 | Some q => exists A, In (q, A, FILE_BLOCK) FB /\ rw_cells asegs m' OUTFILE_ADDR [C8 (Z_to_bv 64 A)]
                 end ->
                 munch [(OUTFILE_ADDR, OUTFILE_ADDR + 8)] m m' -> wmono asegs m m' ->
                 GIOA L RNG (set_outfile o s) CL FB FL m'
  }.

  (* [comment removed for export] *)
  #[using="Type"] Lemma gia_in_block_below : forall (GL : gia_laws) L RNG s CL FB FL m a, GIOA L RNG s CL FB FL m -> in_block (CL ++ FB) a -> 0 < a < ATOP.
  Proof.
    intros GL L RNG s CL FB FL m a G Hin. apply in_block_In in Hin as (b & Hb & Hr).
    destruct (gl_block GL _ _ _ _ _ _ _ _ G Hb) as ((_ & _ & T & _) & P0 & _). lia.
  Qed.
  #[using="Type"] Lemma gia_in_frames_below : forall (GL : gia_laws) L RNG s CL FB FL m a, GIOA L RNG s CL FB FL m -> in_frames FL a -> 0 < a < ATOP.
  Proof.
    intros GL L RNG s CL FB FL m a G Hin. apply in_frames_In in Hin as (fr & Hf & Hr).
    destruct (gl_frames GL _ _ _ _ _ _ _ G) as [FA _]. pose proof (proj1 (Forall_forall _ _) FA fr Hf) as (BAND & T & _).
    unfold ablk, AIMG_HI in BAND. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma gia_in_frame_sh_band : forall (GL : gia_laws) L RNG s CL FB FL m a, GIOA L RNG s CL FB FL m -> in_frame_sh FL a -> 0x7fff7000 <= a < 0x10007fff8000.
  Proof.
    intros GL L RNG s CL FB FL m a G Hin. apply in_frame_sh_In in Hin as (fr & Hf & Hr).
    destruct (gl_frames GL _ _ _ _ _ _ _ G) as [FA _]. pose proof (proj1 (Forall_forall _ _) FA fr Hf) as (BAND & T & A64 & N64 & _).
    rewrite !Z.shiftr_div_pow2 in Hr by lia. change (2 ^ 3) with 8 in Hr.
    unfold ablk, AIMG_HI, KLS in BAND. atop_facts. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma gia_global_unp : forall (GL : gia_laws) L RNG s CL FB FL m A n, GIOA L RNG s CL FB FL m -> In (A, n) client_globals -> unpoisoned m A (A + n).
  Proof.
    intros GL L RNG s CL FB FL m A n G Hin. destruct (gl_globals GL _ _ _ _ _ _ _ G) as [_ FA].
    exact (proj1 (Forall_forall _ _) FA (A, n) Hin).
  Qed.
  Definition gia_global_mobjA__stmt : Prop := forall (GL : gia_laws) L RNG s CL FB FL m A n, GIOA L RNG s CL FB FL m -> In (A, n) client_globals ->
    rng_aimg RNG -> rng_aimg_sh RNG -> mobjA RNG m A n.
  Section Sz5.
  Variables L RNG s CL FB FL m A n : ltac2:(SecDiet.SzSec.tyM 'gia_global_mobjA__stmt "hvvvvvvvvv" @L).
  #[using="Type"] Lemma gia_global_mobjA__body : ltac2:(SecDiet.SzSec.bodyP 'gia_global_mobjA__stmt "hvvvvvvvvv").
  Proof.
    intros GL G Hin RI RS.
 pose proof (gia_global_unp GL _ _ _ _ _ _ _ _ _ G Hin) as U.
    destruct (gl_globals GL _ _ _ _ _ _ _ G) as [W _].
    assert (B : 0x10040 <= A /\ A + n <= 0x602fc0 /\ 0 <= n).
    { clear - Hin. unfold client_globals in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin. }
    destruct B as (B1 & B2 & B3). apply static_mobjA; assumption.
  Qed.
  End Sz5.
  #[using="Type"] Lemma gia_global_mobjA : ltac:(let t := eval cbv delta [gia_global_mobjA__stmt] in gia_global_mobjA__stmt in exact t).
  Proof. intros GL L RNG s CL FB FL m A n. ltac2:(SecDiet.SzSec.closeP 'gia_global_mobjA__body "hvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma gia_stack_sobjA : forall (GL : gia_laws) L RNG s CL FB FL m lo SP A n, GIOA L RNG s CL FB FL m ->
    ATOP + 4096 <= lo -> lo <= SP -> SP <= A -> 0 <= n -> A + n <= al_top L -> rng RNG lo (al_top L - lo) -> sobjA L RNG m SP A n.
  Proof.
    intros GL L RNG s CL FB FL m lo SP A n G LO LS SA Hn HT RS. atop_facts.
    destruct (gl_stack GL _ _ _ _ _ _ _ A n G ltac:(lia) Hn HT) as [U AR].
    split; [exact SA|]. split; [exact HT|]. split; [exact U|]. split; [eapply rng_sub'; [exact RS| lia]|].
    eapply arenaA_sh_rng; [exact AR| lia| exact Hn].
  Qed.
  #[using="Type"] Lemma gia_stack_mobjA : forall (GL : gia_laws) L RNG s CL FB FL m lo A n, GIOA L RNG s CL FB FL m ->
    ATOP + 4096 <= lo -> lo <= A -> 0 <= n -> A + n + 8 <= al_top L -> al_top L <= 2^47 -> rng RNG lo (al_top L - lo) -> mobjA RNG m A n.
  Proof.
    intros GL L RNG s CL FB FL m lo A n G LO LA Hn HT T47 RS. atop_facts.
    destruct (gl_stack GL _ _ _ _ _ _ _ A n G ltac:(lia) Hn ltac:(lia)) as [U AR].
    split; [lia|]. split; [lia|]. split; [exact U|]. split; [eapply rng_sub'; [exact RS| lia]|]. split; [exact AR|].
    unfold app_blk, KHIGH, KEND. split; [lia|]. right. lia.
  Qed.

  #[using="Type"] Lemma gia_global_robjA : forall (GL : gia_laws) L RNG s CL FB FL m A n, GIOA L RNG s CL FB FL m -> In (A, n) client_globals -> A + n <= 0x32000 ->
    rng_aimg RNG -> rng_aimg_sh RNG -> robjA RNG m FL CL A n.
  Proof.
    intros GL L RNG s CL FB FL m A n G Hin HR RI RS. split; [|eapply gia_global_mobjA; eassumption].
    right. exists (A, n). cbn [fst snd]. split; [exact Hin|]. split; [lia|]. split; [lia| exact HR].
  Qed.

  (* [comment removed for export] *)
  Definition std_pre_o (L : alayout) (RNG : footprint) (sp tp : word) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo budget : Z) (m : mem) : Prop :=
    GIOA L RNG s CL FB FL m /\ stk asegs m lo (bv_unsigned sp) /\ ATOP + 4096 <= lo /\ lo + budget <= bv_unsigned sp
    /\ (bv_unsigned sp + 16 < al_top L /\ al_top L <= 2^47) /\ mem_inv asegs m /\ tp = Z_to_bv 64 ATP /\ bv_unsigned sp mod 16 = 0
    /\ (rng RNG lo (al_top L - lo) /\ rng_aimg RNG /\ rng_aimg_sh RNG /\ rng_atls RNG).
  #[local] Abbreviation SPOA := std_pre_o.

  Definition hpost_regs (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (a0v : word) (m' : mem) (ms' : machine_state) : Prop :=
    exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition malloc_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo n : Z),
      SPOA L RNG sp tp s CL FB FL lo MALLOC_STACK m -> a0 = Z_to_bv 64 n -> 1 <= n < 2^29 - 2^16 ->
      unw_okA L RNG m lo AMALLOC_PC sp s0 ra ->
      implMG RNG (pmalloc HO n) s
        (fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ match r with
              | None => False
              | Some q => exists A junk, a0v = Z_to_bv 64 A /\ GIO L RNG' s' ((q, A, n) :: CL) FB FL m'
                          /\ rw_cells asegs m' A [CB (Z.to_nat n) junk]
              end)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 MALLOC_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition calloc_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo cnt sz : Z),
      SPOA L RNG sp tp s CL FB FL lo MALLOC_STACK m -> a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 sz -> 0 <= cnt < 2^32 -> 0 <= sz < 2^32 -> 1 <= cnt * sz <= 3260 ->
      unw_okA L RNG m lo (tp_cpc TP) sp s0 ra ->
      implMG RNG (pcalloc HO cnt sz) s
        (fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ match r with
              | None => False
              | Some q => exists A, a0v = Z_to_bv 64 A /\ GIO L RNG' s' ((q, A, cnt * sz) :: CL) FB FL m'
                          /\ rw_cells asegs m' A [CB (Z.to_nat (cnt * sz)) (repeat (Z_to_bv 8 0) (Z.to_nat (cnt * sz)))]
              end)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 CALLOC_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition realloc_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (C1 C2 FB : list cblk) (FL : list fblock) (q : hptr) (A sz lo n : Z) (bs : list byte),
      SPOA L RNG sp tp s (C1 ++ (q, A, sz) :: C2) FB FL lo REALLOC_STACK m -> a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 1 <= n < 2^29 - 2^16 ->
      rw_cells asegs m A [CB (Z.to_nat sz) bs] ->
      unw_okA L RNG m lo (tp_rpc TP) sp s0 ra ->
      implMG RNG (prealloc HO q n) s
        (fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL (C1 ++ C2) (bv_unsigned sp)) m m'
           /\ match r with
              | None => False
              | Some q' => exists A' junk, a0v = Z_to_bv 64 A' /\ GIO L RNG' s' ((q', A', n) :: C1 ++ C2) FB FL m'
                          /\ rw_cells asegs m' A' [CB (Z.to_nat (Z.min sz n)) (firstn (Z.to_nat (Z.min sz n)) bs); CB (Z.to_nat (n - Z.min sz n)) junk]
              end)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 REALLOC_ENTRY) fc None m (seg_rom asegs)).

  Definition free_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (C1 C2 FB : list cblk) (FL : list fblock) (q : hptr) (A n lo : Z),
      SPOA L RNG sp tp s (C1 ++ (q, A, n) :: C2) FB FL lo FREE_STACK m -> a0 = Z_to_bv 64 A ->
      unw_okA L RNG m lo AFREE_PC sp s0 ra ->
      implMG RNG (pfree HO q) s
        (fun _ s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL (C1 ++ C2) (bv_unsigned sp)) m m'
           /\ GIO L RNG' s' (C1 ++ C2) FB FL m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREE_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition free_null_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo : Z),
      SPOA L RNG sp tp s CL FB FL lo FREE_STACK m -> a0 = Z_to_bv 64 0 ->
      unw_okA L RNG m lo AFREE_PC sp s0 ra ->
      evtF asegs RNG (fun ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ GIO L RNG s CL FB FL m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREE_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition fenter_stmt_o (k SYM : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo req : Z)
           (f : fframe) (A : Type) (body : MP A) (Q : A -> PS -> footprint -> machine_state -> Prop),
      SPOA L RNG sp tp s CL FB FL lo FAKE_STACK m -> a0 = Z_to_bv 64 req -> 0 < req <= ff_size f ->
      ~ In f (map fb_fn FL) -> ff_class f = k ->
      (forall (Fb : Z) (s' : PS) (m' : mem) (j0 j1 j2 : word) (junk : list byte) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
         GIO L RNG s' CL FB ((f, Fb, ff_size f) :: FL) m' ->
         ps_outfile s' = ps_outfile s -> ps_libc s' = ps_libc s -> ps_tls s' = ps_tls s ->
         mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp) -> agrees_on (client_keeps FL CL (bv_unsigned sp)) m m' ->
         0 < Fb -> length junk = Z.to_nat (ff_size f - 32) ->
         rw_cells asegs m' Fb [C8 j0; C8 j1; C8 j2; CB (Z.to_nat (ff_size f - 32)) junk; C8 (Z_to_bv 64 (fflagA L f Fb))] ->
         rw_cells asegs m' (Z.shiftr Fb 3 + 2147450880) [CB (Z.to_nat (ff_size f / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (ff_size f / 8)))] ->
         implMG RNG body s' Q
           (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 Fb) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom asegs))) ->
      implMG RNG (fo_enter FO _ f body) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 SYM) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition fenter7_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo req : Z)
           (f : fframe) (A : Type) (body : MP A) (Q : A -> PS -> footprint -> machine_state -> Prop),
      SPOA L RNG sp tp s CL FB FL lo FAKE_STACK m -> a0 = Z_to_bv 64 req -> 0 < req <= ff_size f -> req mod 8 = 0 ->
      ~ In f (map fb_fn FL) -> ff_class f = 7 ->
      (forall (Fb : Z) (s' : PS) (m' : mem) (j0 j1 j2 : word) (junk sjunk : list byte) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
         GIO L RNG s' CL FB ((f, Fb, ff_size f) :: FL) m' ->
         ps_outfile s' = ps_outfile s -> ps_libc s' = ps_libc s -> ps_tls s' = ps_tls s ->
         mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp) -> agrees_on (client_keeps FL CL (bv_unsigned sp)) m m' ->
         0 < Fb -> length junk = Z.to_nat (ff_size f - 32) -> length sjunk = Z.to_nat ((ff_size f - req) / 8) ->
         rw_cells asegs m' Fb [C8 j0; C8 j1; C8 j2; CB (Z.to_nat (ff_size f - 32)) junk; C8 (Z_to_bv 64 (fflagA L f Fb))] ->
         rw_cells asegs m' (Z.shiftr Fb 3 + 2147450880)
           [CB (Z.to_nat (req / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (req / 8))); CB (Z.to_nat ((ff_size f - req) / 8)) sjunk] ->
         implMG RNG body s' Q
           (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 Fb) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom asegs))) ->
      implMG RNG (fo_enter FO _ f body) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 STACK_MALLOC_7) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition fret_inline_law : Prop :=
    forall (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (f : fframe) (Fb : Z) (m m' : mem)
           (A : Type) (x : A) (Q : A -> PS -> footprint -> machine_state -> Prop) (ms : machine_state),
      GIO L RNG s CL FB ((f, Fb, ff_size f) :: FL) m -> ff_class f <= 6 ->
      munch [(fflagA L f Fb, fflagA L f Fb + 1)] m m' -> wmono asegs m m' -> rw_cells asegs m' (fflagA L f Fb) [C1 (Z_to_bv 8 0)] ->
      (forall s' : PS, GIO L RNG s' CL FB FL m' -> ps_outfile s' = ps_outfile s -> ps_libc s' = ps_libc s -> ps_tls s' = ps_tls s ->
         evtF asegs RNG (Q x s' RNG) ms) ->
      implMG RNG (fo_ret FO _ f x) s Q ms.

  (* [comment removed for export] *)
  Definition ffree7_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo Fb req : Z)
           (f : fframe) (A : Type) (x : A) (Q : A -> PS -> footprint -> machine_state -> Prop),
      SPOA L RNG sp tp s CL FB ((f, Fb, ff_size f) :: FL) lo FAKE_STACK m -> ff_class f = 7 ->
      a0 = Z_to_bv 64 Fb -> a1 = Z_to_bv 64 req -> 0 < req <= ff_size f -> req mod 8 = 0 ->
      rw_cells asegs m (Fb + ff_size f - 8) [C8 (Z_to_bv 64 (fflagA L f Fb))] ->
      (forall (s' : PS) (m' : mem) (a0' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
         GIO L RNG s' CL FB FL m' -> ps_outfile s' = ps_outfile s -> ps_libc s' = ps_libc s -> ps_tls s' = ps_tls s ->
         mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp) -> agrees_on (client_keeps FL CL (bv_unsigned sp)) m m' ->
         evtF asegs RNG (Q x s' RNG)
           (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom asegs))) ->
      implMG RNG (fo_ret FO _ f x) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 STACK_FREE_7) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition set_shadow_stmt (SYM v : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (RNG : footprint) (lo SA n : Z) (old : list byte),
      mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo + FAKE_STACK <= bv_unsigned sp -> ATOP + 4096 <= lo ->
      artcells m -> rw_cells asegs m GOT_MEMSET [C8 (Z_to_bv 64 0xa7360)] ->   (* [comment removed for export] *)
      a0 = Z_to_bv 64 SA -> a1 = Z_to_bv 64 n -> 0 < SA -> 0 < n <= 4096 ->
      rw_cells asegs m SA [CB (Z.to_nat n) old] -> rng RNG SA n -> rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG ->
      evtF asegs RNG (fun ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ munch [(bv_unsigned sp - FAKE_STACK, bv_unsigned sp); (SA, SA + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
           /\ stk asegs m' lo (bv_unsigned sp)
           /\ rw_cells asegs m' SA [CB (Z.to_nat n) (repeat (Z_to_bv 8 v) (Z.to_nat n))])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 SYM) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition strlen_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo P : Z) (bs slack : list byte),
      SPOA L RNG sp tp s CL FB FL lo STDIO_STACK m -> a0 = Z_to_bv 64 P ->
      bytes_at asegs m P (bs ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) bs -> Z.of_nat (length bs) < 2^24 ->
      (- (P + Z.of_nat (length bs) + 1)) mod 8 <= Z.of_nat (length slack) ->
      robjA RNG m FL CL P (Z.of_nat (length bs) + 1) -> rng RNG P (Z.of_nat (length bs) + 1 + Z.of_nat (length slack)) ->
      evtF asegs RNG (fun ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ munch [(bv_unsigned sp - STDIO_STACK, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
           /\ stk asegs m' lo (bv_unsigned sp)
           /\ a0v = Z_to_bv 64 (Z.of_nat (length bs)))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 STRLEN_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition PCAP_TLS_ERRBUF : Z := 20.
  Definition strerror_r_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo e : Z),
      SPOA L RNG sp tp s CL FB FL lo STDIO_STACK m ->
      a0 = Z_to_bv 64 (s32 e) -> a1 = Z_to_bv 64 (ATP + PCAP_TLS_ERRBUF) -> a2 = Z_to_bv 64 256 -> -2^31 <= e < 2^31 ->
      evtF asegs RNG (fun ms' => exists a0v m' rest, hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ a0v = Z_to_bv 64 0
           /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ GIO L RNG s CL FB FL m'
           /\ rw_cells asegs m' (ATP + PCAP_TLS_ERRBUF) [CB (length (Fmt.strerror e) + 1) (map (fun z => Z_to_bv 8 z) (Fmt.strerror e) ++ [Z_to_bv 8 0]);
                                                         CB (255 - length (Fmt.strerror e)) rest])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 STRERROR_R_ENTRY) fc None m (seg_rom asegs)).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition mode_ok (wr : bool) (md : list byte) : Prop :=
    if wr then (md = [Z_to_bv 8 119] \/ md = [Z_to_bv 8 119; Z_to_bv 8 98])     (* [comment removed for export] *)
    else (md = [Z_to_bv 8 114] \/ md = [Z_to_bv 8 114; Z_to_bv 8 98]).          (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition mode_lit (wr : bool) (MODE : Z) (md : list byte) : Prop :=
    if wr then (MODE = 0x21020 /\ md = [Z_to_bv 8 119]) \/ (MODE = 0x211a0 /\ md = [Z_to_bv 8 119; Z_to_bv 8 98])   (* [comment removed for export] *)
    else (MODE = STR_RB /\ md = [Z_to_bv 8 114; Z_to_bv 8 98]).                                                  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition fopen_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (trC : list Z) (lo NAME MODE : Z) (name md : list byte) (wr : bool),
      SPOA L RNG sp tp s CL FB FL lo STDIO_STACK m ->
      ucallerA 0%nat L m sp s0 ra trC -> tp_fopen TP L (bv_unsigned ra) trC -> a0 = Z_to_bv 64 NAME -> a1 = Z_to_bv 64 MODE ->
      bytes_at asegs m NAME (name ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) name -> (1 <= length name <= 4095)%nat ->
      open_name_ok wr name ->   (* [comment removed for export] *)
      robjA RNG m FL CL NAME (Z.of_nat (length name) + 1) ->
      bytes_at asegs m MODE (md ++ [Z_to_bv 8 0]) -> mode_lit wr MODE md -> robjA RNG m FL CL MODE (Z.of_nat (length md) + 1) ->
      implMG RNG (s_fopen HO (map bv_unsigned name) wr) s
        (fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ match r with
              | None => a0v = Z_to_bv 64 0 /\ GIO L RNG' s' CL FB FL m'
                        /\ rw_cells asegs m' (ATP + -164) [C4 (Z_to_bv 64 (lc_errno (ps_libc s')))]   (* [comment removed for export] *)
                        /\ 0 <= lc_errno (ps_libc s') < 2^31
              | Some f => exists Af, a0v = Z_to_bv 64 Af /\ GIO L RNG' s' CL ((f, Af, FILE_BLOCK) :: FB) FL m'
              end)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FOPEN_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition fclose_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL F1 F2 : list cblk) (FL : list fblock) (trC : list Z) (f : hptr) (Af lo : Z),
      SPOA L RNG sp tp s CL (F1 ++ (f, Af, FILE_BLOCK) :: F2) FL lo STDIO_STACK m ->
      ucallerA 0%nat L m sp s0 ra trC -> tp_fclose TP L (bv_unsigned ra) trC -> a0 = Z_to_bv 64 Af -> ps_outfile s <> Some f ->
      implMG RNG (s_fclose HO f) s
        (fun _ s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ GIO L RNG' s' CL (F1 ++ F2) FL m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FCLOSE_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition fread_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (f : hptr) (Af D n lo : Z) (junk : list byte),
      SPOA L RNG sp tp s CL FB FL lo STDIO_STACK m -> In (f, Af, FILE_BLOCK) FB ->
      a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 n -> a3 = Z_to_bv 64 Af -> 0 <= n <= 2^30 ->
      rw_cells asegs m D [CB (Z.to_nat n) junk] -> cobjA RNG m FL CL D n ->
      implMG RNG (s_fread HO f D n) s
        (fun got s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m' junk', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
           /\ agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ ~ (D <= a < D + n)) m m'
           /\ GIO L RNG' s' CL FB FL m'
           /\ a0v = Z_to_bv 64 (zlength got) /\ 0 <= zlength got <= n /\ Forall (fun z => 0 <= z < 256) got
           /\ rw_cells asegs m' D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junk'])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREAD_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition ferror_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (f : hptr) (Af lo : Z),
      SPOA L RNG sp tp s CL FB FL lo STDIO_STACK m -> In (f, Af, FILE_BLOCK) FB -> a0 = Z_to_bv 64 Af ->
      implMG RNG (s_ferror HO f) s
        (fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ GIO L RNG' s' CL FB FL m' /\ s' = s /\ a0v = Z_to_bv 64 (Z.b2z r)
           (* [comment removed for export] *)
           /\ (r = true -> rw_cells asegs m' (ATP + -164) [C4 (Z_to_bv 64 (lc_errno (ps_libc s')))] /\ 0 <= lc_errno (ps_libc s') < 2^31))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FERROR_ENTRY) fc None m (seg_rom asegs)).

  Definition fileno_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (f : hptr) (Af lo : Z),
      SPOA L RNG sp tp s CL FB FL lo STDIO_STACK m -> In (f, Af, FILE_BLOCK) FB -> a0 = Z_to_bv 64 Af ->
      implMG RNG (s_fileno HO f) s
        (fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ GIO L RNG' s' CL FB FL m' /\ s' = s /\ a0v = Z_to_bv 64 r /\ 0 <= r < 2^31)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FILENO_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition fprintf_dd_stmt_o (FMT : Z) (mk : Z -> Z -> list (list Z)) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (f : hptr) (Af lo v1 v2 : Z),
      SPOA L RNG sp tp s CL FB FL lo STDIO_STACK m -> In (f, Af, FILE_BLOCK) FB ->
      a0 = Z_to_bv 64 Af -> a1 = Z_to_bv 64 FMT -> a2 = sx32 (Z_to_bv 64 v1) -> a3 = sx32 (Z_to_bv 64 v2) -> 0 <= v1 < 2^32 -> 0 <= v2 < 2^32 ->
      implMG RNG (s_fprintf HO f (mk v1 v2)) s
        (fun _ s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ GIO L RNG' s' CL FB FL m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FPRINTF_ENTRY) fc None m (seg_rom asegs)).

  Definition fprintf_s_stmt_o (FMT : Z) (mk : list Z -> list (list Z)) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (f : hptr) (Af lo P : Z) (str slack : list byte),
      SPOA L RNG sp tp s CL FB FL lo STDIO_STACK m -> In (f, Af, FILE_BLOCK) FB ->
      a0 = Z_to_bv 64 Af -> a1 = Z_to_bv 64 FMT -> a2 = Z_to_bv 64 P ->
      bytes_at asegs m P (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) < 2^24 ->
      (- (P + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->   (* [comment removed for export] *)
      cobjA RNG m FL CL P (Z.of_nat (length str) + 1 + Z.of_nat (length slack)) ->   (* [comment removed for export] *)
      Z.of_nat (length slack) <= 2^24 ->   (* [comment removed for export] *)
      implMG RNG (s_fprintf HO f (mk (map bv_unsigned str))) s
        (fun _ s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ GIO L RNG' s' CL FB FL m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FPRINTF_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition fmt_at (m : mem) (FMTA : Z) (fs : string) : Prop :=
    bytes_at asegs m FMTA (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string fs) ++ [Z_to_bv 8 0])
    /\ 0x10000 <= FMTA /\ FMTA + Z.of_nat (String.length fs) + 1 <= 0x32000
    /\ In (FMTA, Z.of_nat (String.length fs) + 1) client_globals.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition conv_ok (c : conv) (a : farg) : bool :=
    match c, a with
    | Cs, AStr _ => true
    | Cd, AInt _ => true | Cu, AInt _ => true | Czu, AInt _ => true | C08x, AInt _ => true
    | _, _ => false
    end.
  Fixpoint items_ok (its : list fitem) (args : list farg) : bool :=
    match its with
    | [] => match args with [] => true | _ => false end
    | FLit l :: its' => forallb (fun c => negb (c =? 0) && negb (c =? 37)) l && items_ok its' args
    | FConv c :: its' => match args with a :: args' => conv_ok c a && items_ok its' args' | [] => false end
    | FBad _ :: _ => false
    end.
  Definition fmt_ok (fs : string) (args : list farg) : bool :=
    items_ok (fmt fs) args && (Z.of_nat (String.length fs) <? 4096).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition slocA (tls : bool) (FL : list fblock) (CL : list cblk) (P n k : Z) : Prop :=
    clocA FL CL P (n + k)
    \/ (exists g, In g client_globals /\ fst g <= P /\ P + n <= fst g + snd g /\ fst g + snd g <= 0x32000 /\ P + n + k <= 0x32000)
    \/ (tls = true /\ ATP + -200 <= P /\ P + n + k <= ATP + -200 + 504).
  Definition farg_word (tls : bool) (L : alayout) (RNG : footprint) (FL : list fblock) (CL : list cblk) (SP D dn : Z) (m : mem) (a : farg) (w : word) : Prop :=
    match a with
    | AInt z => w = Z_to_bv 64 z
    | AStr cs => exists P bs slack, w = Z_to_bv 64 P /\ bytes_at asegs m P (bs ++ Z_to_bv 8 0 :: slack) /\ ~ In (Z_to_bv 8 0) bs
                 /\ cs = map bv_unsigned bs /\ Z.of_nat (length bs) < 2^24
                 /\ (- (P + Z.of_nat (length bs) + 1)) mod 8 <= Z.of_nat (length slack)
                 /\ (P + Z.of_nat (length bs) + 1 + Z.of_nat (length slack) <= D \/ D + dn <= P)
                 (* [comment removed for export] *)
                 /\ slocA tls FL CL P (Z.of_nat (length bs) + 1) (Z.of_nat (length slack))
                 /\ mobjA RNG m P (Z.of_nat (length bs) + 1)
                 /\ rng RNG P (Z.of_nat (length bs) + 1 + Z.of_nat (length slack))
    end.

  (* [comment removed for export] *)
  Definition snprintf_spec_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo DST n FMTA : Z) (fs : string) (args : list farg) (junk : list byte),
      SPOA L RNG sp tp s CL FB FL lo STDIO_STACK m ->
      a0 = Z_to_bv 64 DST -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 FMTA -> 1 <= n < 2^31 -> fmt_at m FMTA fs -> fmt_ok fs args = true ->
      (length args <= 3)%nat -> Forall2 (farg_word true L RNG FL CL (bv_unsigned sp) DST n m) args (firstn (length args) [a3; a4; a5]) ->
      rw_cells asegs m DST [CB (Z.to_nat n) junk] -> cobjA RNG m FL CL DST n ->
      evtF asegs RNG (fun ms' => exists a0v m' junk', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ munch [(bv_unsigned sp - STDIO_STACK, bv_unsigned sp); (DST, DST + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
           /\ stk asegs m' lo (bv_unsigned sp)
           /\ a0v = Z_to_bv 64 (snprintf_ret (fmt fs) args)
           /\ rw_cells asegs m' DST [CB (length (Fmt.snprintf n fs args) + 1) (map b8 (Fmt.snprintf n fs args) ++ [Z_to_bv 8 0]);
                                   CB (Z.to_nat n - length (Fmt.snprintf n fs args) - 1) junk'])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 SNPRINTF_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition vsnprintf_spec_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo DST n FMTA AP : Z) (fs : string) (args : list farg)
           (ws : list word) (junk : list byte),
      SPOA L RNG sp tp s CL FB FL lo STDIO_STACK m ->
      a0 = Z_to_bv 64 DST -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 FMTA -> a3 = Z_to_bv 64 AP -> 1 <= n < 2^31 -> fmt_at m FMTA fs -> fmt_ok fs args = true ->
      length ws = length args -> (length args <= 4)%nat -> Forall2 (farg_word true L RNG FL CL (bv_unsigned sp) DST n m) args ws ->
      rw_cells asegs m AP (map C8 ws) -> bv_unsigned sp <= AP -> AP + 8 * Z.of_nat (length ws) <= al_top L ->
      (AP + 8 * Z.of_nat (length ws) <= DST \/ DST + n <= AP) ->
      rw_cells asegs m DST [CB (Z.to_nat n) junk] -> cobjA RNG m FL CL DST n ->
      evtF asegs RNG (fun ms' => exists a0v m' junk', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ munch [(bv_unsigned sp - STDIO_STACK, bv_unsigned sp); (DST, DST + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
           /\ stk asegs m' lo (bv_unsigned sp)
           /\ a0v = Z_to_bv 64 (snprintf_ret (fmt fs) args)
           /\ rw_cells asegs m' DST [CB (length (Fmt.snprintf n fs args) + 1) (map b8 (Fmt.snprintf n fs args) ++ [Z_to_bv 8 0]);
                                   CB (Z.to_nat n - length (Fmt.snprintf n fs args) - 1) junk'])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 VSNPRINTF_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition leaf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (v : word) (fr lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - fr, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ a0 = v.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition LT_TABLE : Z := 0x22000.
  Definition linktype_to_dlt_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (RNG : footprint) (lo lt : Z),
      mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp -> ATOP + 4096 <= lo ->
      artcells m -> unpoisoned m LT_TABLE (LT_TABLE + 28) ->
      rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng_aimg_sh RNG ->
      a0 = Z_to_bv 64 lt -> 0 <= lt < 2^32 ->
      evtF asegs RNG (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 (linktype_to_dlt lt)) 16 lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 LINKTYPE_TO_DLT_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition max_snaplen_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (RNG : footprint) (lo dlt : Z),
      mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) ->
      a0 = Z_to_bv 64 dlt -> 0 <= dlt < 2^64 ->
      evtF asegs RNG (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 (max_snaplen_for_dlt dlt)) 0 lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 MAX_SNAPLEN_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition adjust_snapshot_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (RNG : footprint) (lo lt snaplen : Z),
      mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) ->
      a0 = Z_to_bv 64 lt -> 0 <= lt < 2^31 -> a1 = Z_to_bv 64 (s32 snaplen) -> 0 <= snaplen < 2^32 ->
      evtF asegs RNG (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 (pcapint_adjust_snapshot lt snaplen)) 0 lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_ADJUST_SNAPSHOT_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ONESHOT_STACK : Z := 32 + 0x2000.
  Definition oneshot_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (RNG : footprint) (lo U HD PKT SRC : Z) (pd w0 w1 w2 o0 o1 o2 : word) (pkc : cell),
      a0 = Z_to_bv 64 U -> a1 = Z_to_bv 64 SRC ->
      rw_cells asegs m U [C8 (Z_to_bv 64 HD); C8 (Z_to_bv 64 PKT); C8 pd] ->
      rw_cells asegs m SRC [C8 w0; C8 w1; C8 w2] ->
      rw_cells asegs m HD [C8 o0; C8 o1; C8 o2] ->
      rw_cells asegs m PKT [pkc] -> csize pkc = 8%nat ->
      (HD + 24 <= U \/ U + 24 <= HD) -> (HD + 24 <= SRC \/ SRC + 24 <= HD) -> (HD + 24 <= PKT \/ PKT + 8 <= HD) ->
      (PKT + 8 <= U \/ U + 24 <= PKT) -> (PKT + 8 <= SRC \/ SRC + 24 <= PKT) ->
      mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo + ONESHOT_STACK <= bv_unsigned sp -> ATOP + 4096 <= lo ->
      artcells m ->
      aobjA RNG m U 24 -> aobjA RNG m SRC 24 -> aobjA RNG m HD 24 -> aobjA RNG m PKT 8 ->
      U + 24 <= ATOP -> SRC + 24 <= ATOP -> HD + 24 <= ATOP -> PKT + 8 <= ATOP ->
      U mod 8 = 0 -> PKT mod 8 = 0 -> HD mod 8 = 0 -> SRC mod 8 = 0 ->
      rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_atls RNG ->
      evtF asegs RNG (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
          ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (ret_pc ra) fc None m' (seg_rom asegs)
          /\ munch [(bv_unsigned sp - ONESHOT_STACK, bv_unsigned sp); (HD, HD + 24); (PKT, PKT + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
          /\ stk asegs m' lo (bv_unsigned sp)
          /\ rw_cells asegs m' U [C8 (Z_to_bv 64 HD); C8 (Z_to_bv 64 PKT); C8 pd]
          /\ rw_cells asegs m' SRC [C8 w0; C8 w1; C8 w2]
          /\ rw_cells asegs m' HD [C8 w0; C8 w1; C8 w2]
          /\ rw_cells asegs m' PKT [C8 a2])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (pk_oneshot PK)) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition pcap_strerror_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo e : Z),
      SPOA L RNG sp tp s CL FB FL lo PCAP_L0_STACK m ->
      a0 = Z_to_bv 64 (s32 e) -> -2^31 <= e < 2^31 ->
      evtF asegs RNG (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' rest,
          ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (ATP + PCAP_TLS_ERRBUF)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (ret_pc ra) fc None m' (seg_rom asegs)
          /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
          /\ GIO L RNG s CL FB FL m'
          /\ rw_cells asegs m' (ATP + PCAP_TLS_ERRBUF) [CB (length (Fmt.strerror e) + 1) (map b8 (Fmt.strerror e) ++ [Z_to_bv 8 0]);
                                                        CB (255 - length (Fmt.strerror e)) rest])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_STRERROR_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition fmt_errmsg_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo EB FMTA e : Z) (fs : string) (args : list farg)
           (junk : list byte),
      SPOA L RNG sp tp s CL FB FL lo PCAP_L1_STACK m -> ~ In FF_FMT_ERRMSG (map fb_fn FL) ->
      a0 = Z_to_bv 64 EB -> a1 = Z_to_bv 64 256 -> a2 = Z_to_bv 64 (s32 e) -> -2^31 <= e < 2^31 -> a3 = Z_to_bv 64 FMTA ->
      fmt_at m FMTA fs -> fmt_ok fs args = true -> (length args <= 1)%nat -> Forall2 (farg_word false L RNG FL CL (bv_unsigned sp) EB 256 m) args (firstn (length args) [a4]) ->
      rw_cells asegs m EB [CB 256 junk] -> cobjA RNG m FL CL EB 256 -> EB mod 8 = 0 ->
      implMG RNG (fo_enter FO _ FF_FMT_ERRMSG (fo_ret FO _ FF_FMT_ERRMSG (fmt_errmsg fs args e))) s
        (fun r s' RNG' ms' => fp_le RNG RNG' /\ r = fmt_errmsg fs args e /\
          exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' junk',
          ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (ret_pc ra) fc None m' (seg_rom asegs)
          /\ ps_outfile s' = ps_outfile s /\ ps_libc s' = ps_libc s /\ ps_tls s' = ps_tls s
          /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
          /\ agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256)) m m'
          /\ GIO L RNG' s' CL FB FL m'
          /\ rw_cells asegs m' EB [CB (length (fmt_errmsg fs args e) + 1) (map b8 (fmt_errmsg fs args e) ++ [Z_to_bv 8 0]);
                                  CB (255 - length (fmt_errmsg fs args e)) junk'])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_FMT_ERRMSG_ENTRY) fc None m (seg_rom asegs)).

  Definition pcap_post {A} (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (FL : list fblock) (CLc : list cblk) (lo : Z) (m : mem)
      (X : A -> PS -> word -> mem -> list cblk -> list cblk -> Prop) : A -> PS -> footprint -> machine_state -> Prop :=
    fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m' PB' FB', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CLc (bv_unsigned sp)) m m'
      /\ GIO L RNG' s' (CLc ++ PB') FB' FL m' /\ X r s' a0v m' PB' FB'.

  (* [comment removed for export] *)
  Definition pcap_stats_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CLc PB FB : list cblk) (FL : list fblock) (trC : list Z) (lo P : Z) (p : pcapT),
      SPOA L RNG sp tp s (CLc ++ PB) FB FL lo PCAP_L1_STACK m ->
      ucallerA (depth_pcap_stats) L m sp s0 ra trC -> traces_pcap_stats TP L (bv_unsigned ra) trC -> nofr (frames_pcap_stats) FL -> PCRC P p PB FB m -> a0 = Z_to_bv 64 P ->
      implMG RNG (Pcap.pcap_stats MOps p) s
        (pcap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CLc lo m
           (fun r s' a0v m' PB' FB' => PB' = PB /\ FB' = FB /\ s' = s /\ a0v = Z_to_bv 64 (fst r) /\ fst r = -1 /\ PCRC P (snd r) PB FB m'))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_STATS_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition next_packet_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (FL : list fblock) (CLc : list cblk) (FB : list cblk) (lo P HA DA : Z) (m : mem) (o : option hptr) : (Z * pkthdr * pcapT) -> PS -> footprint -> machine_state -> Prop :=
    fun r s' RNG' ms' => fp_le RNG RNG' /\ let '(st, h, p') := r in
      exists a0v m' PB' (dw : cell), hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ ps_outfile s' = o /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8)) m m'
      /\ GIO L RNG' s' (CLc ++ PB') FB FL m' /\ (st <> -1 -> PCR P p' PB' FB m') /\ (st = -1 -> PCRC P p' PB' FB m')
      /\ a0v = Z_to_bv 64 st /\ (st = 1 \/ st = 0 \/ st = -1)
      /\ (st = 1 -> rw_cells asegs m' HA (hdr_cells h) /\ 0 <= h_caplen h < 2^32 /\ 0 <= h_len h < 2^32)
      /\ (st <> 1 -> exists hcs', cells_size hcs' = 24%nat /\ rw_cells asegs m' HA hcs')
      /\ rw_cells asegs m' DA [dw] /\ csize dw = 8%nat.

  Definition next_packet_op_stmt_for (ng : bool) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CLc PB FB : list cblk) (FL : list fblock) (trC : list Z) (lo P HA DA : Z) (p : pcapT) (fuel : nat)
           (hcs : list cell) (dc : cell),
      SPOA L RNG sp tp s (CLc ++ PB) FB FL lo PCAP_L2_STACK m ->
      ucallerA (depth_next_packet_op ng) L m sp s0 ra trC -> traces_next_packet_op TP ng L (bv_unsigned ra) trC -> nofr (frames_next_packet_op ng) FL -> PCR P p PB FB m -> is_ng p = ng -> bv_unsigned sp + 16 <= bv_unsigned s0 ->   (* [comment removed for export] *)
     
      a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 HA -> a2 = Z_to_bv 64 DA ->
      rw_cells asegs m HA hcs -> cells_size hcs = 24%nat -> rw_cells asegs m DA [dc] -> csize dc = 8%nat ->
      cobjA RNG m FL CLc HA 24 -> cobjA RNG m FL CLc DA 8 -> (HA + 24 <= DA \/ DA + 8 <= HA) ->   (* [comment removed for export] *) HA mod 8 = 0 -> DA mod 8 = 0 ->
      implMG RNG (next_packet_op MOps PR fuel p) s
        (next_packet_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CLc FB lo P HA DA m (ps_outfile s))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (np_entry p)) fc None m (seg_rom asegs)).
  Definition pcap_next_packet_stmt : Prop := next_packet_op_stmt_for false.
  Definition pcap_ng_next_packet_stmt : Prop := next_packet_op_stmt_for true.

  (* [comment removed for export] *)
  Definition offline_read_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CLc PB FB : list cblk) (FL : list fblock) (trC : list Z) (lo P U PKT : Z) (p : pcapT) (fuel : nat)
           (pd : word) (pkc : cell),
      SPOA L RNG sp tp s (CLc ++ PB) FB FL lo PCAP_L3_STACK m ->
      ucallerA (depth_offline_read) L m sp s0 ra trC -> traces_offline_read TP L (bv_unsigned ra) trC -> nofr (frames_offline_read) FL -> PCR P p PB FB m ->
      a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 (pk_oneshot PK) -> a3 = Z_to_bv 64 U ->
      rw_cells asegs m U [C8 (Z_to_bv 64 (P + PCAP_HDR_OFF)); C8 (Z_to_bv 64 PKT); C8 pd] -> rw_cells asegs m PKT [pkc] -> csize pkc = 8%nat ->
      cobjA RNG m FL CLc U 24 -> cobjA RNG m FL CLc PKT 8 -> (U + 24 <= PKT \/ PKT + 8 <= U) ->
      U mod 8 = 0 -> PKT mod 8 = 0 ->
      implMG RNG (pcapint_offline_read_1 MOps PR fuel p) s
        (fun r s' RNG' ms' => fp_le RNG RNG' /\ let '(st, p') := r in
           exists a0v m' PB' (pk' : cell), hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
           /\ agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (PKT <= a < PKT + 8)) m m'
           /\ GIO L RNG' s' (CLc ++ PB') FB FL m' /\ (st <> -1 -> PCR P p' PB' FB m') /\ (st = -1 -> PCRC P p' PB' FB m')
           /\ a0v = Z_to_bv 64 st /\ (st = 1 \/ st = 0 \/ st = -1)
           /\ rw_cells asegs m' U [C8 (Z_to_bv 64 (P + PCAP_HDR_OFF)); C8 (Z_to_bv 64 PKT); C8 pd]
           /\ rw_cells asegs m' PKT [pk'] /\ csize pk' = 8%nat)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_OFFLINE_READ_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition pcap_next_ex_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CLc PB FB : list cblk) (FL : list fblock) (trC : list Z) (lo P HP PKT : Z) (p : pcapT) (fuel : nat)
           (hc pkc : cell),
      SPOA L RNG sp tp s (CLc ++ PB) FB FL lo PCAP_L4_STACK m ->
      ucallerA (depth_pcap_next_ex) L m sp s0 ra trC -> traces_pcap_next_ex TP L (bv_unsigned ra) trC -> nofr (frames_pcap_next_ex) FL -> PCR P p PB FB m ->
      a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 HP -> a2 = Z_to_bv 64 PKT ->
      rw_cells asegs m HP [hc] -> csize hc = 8%nat -> rw_cells asegs m PKT [pkc] -> csize pkc = 8%nat ->
      cobjA RNG m FL CLc HP 8 -> cobjA RNG m FL CLc PKT 8 -> (HP + 8 <= PKT \/ PKT + 8 <= HP) ->
      HP mod 8 = 0 -> PKT mod 8 = 0 ->
      implMG RNG (Pcap.pcap_next_ex MOps PR fuel p) s
        (fun r s' RNG' ms' => fp_le RNG RNG' /\ let '(st, p') := r in
           exists a0v m' PB' (pk' : cell), hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
           /\ agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HP <= a < HP + 8) /\ ~ (PKT <= a < PKT + 8)) m m'
           /\ GIO L RNG' s' (CLc ++ PB') FB FL m' /\ (st <> -1 -> PCR P p' PB' FB m') /\ (st = -1 -> PCRC P p' PB' FB m')
           /\ a0v = Z_to_bv 64 st /\ (st = 1 \/ st = -2 \/ st = -1)
           /\ rw_cells asegs m' HP [C8 (Z_to_bv 64 (P + PCAP_HDR_OFF))]
           /\ rw_cells asegs m' PKT [pk'] /\ csize pk' = 8%nat)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_NEXT_EX_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition cleanup_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (FL : list fblock) (CLc FB1 FB2 : list cblk) (lo P B Af : Z) (p : pcapT) (m : mem) (o : option hptr) : unit -> PS -> footprint -> machine_state -> Prop :=
    fun _ s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m' j', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ ps_outfile s' = o /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CLc (bv_unsigned sp)) m m'
      /\ GIO L RNG' s' (CLc ++ [(pc_self p, P, psize p)]) (FB1 ++ FB2) FL m'
      /\ rw_cells asegs m' P (pcap_cells p P B Af j').

  Definition sf_cleanup_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CLc FB1 FB2 : list cblk) (FL : list fblock) (trC : list Z) (lo P B Af : Z) (p : pcapT) (j : pcap_junk),
      SPOA L RNG sp tp s (CLc ++ [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p)]) (FB1 ++ (pc_rfile p, Af, FILE_BLOCK) :: FB2) FL lo PCAP_L3_STACK m ->
      ucallerA (depth_sf_cleanup) L m sp s0 ra trC -> traces_sf_cleanup TP L (bv_unsigned ra) trC -> nofr (frames_sf_cleanup) FL ->
      rw_cells asegs m P (pcap_cells p P B Af j) -> a0 = Z_to_bv 64 P -> ps_outfile s <> Some (pc_rfile p) ->
      implMG RNG (Pcap.pcapint_sf_cleanup MOps PR p) s
        (cleanup_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CLc FB1 FB2 lo P B Af p m (ps_outfile s))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (pk_cleanup_sf PK)) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition ng_cleanup_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CLc PB FB : list cblk) (FL : list fblock) (trC : list Z) (lo P : Z) (p : pcapT),
      SPOA L RNG sp tp s (CLc ++ PB) FB FL lo PCAP_L3_STACK m ->
      ucallerA (depth_ng_cleanup) L m sp s0 ra trC -> traces_ng_cleanup TP L (bv_unsigned ra) trC -> nofr (frames_ng_cleanup) FL -> PCRC P p PB FB m -> is_ng p = true ->
      a0 = Z_to_bv 64 P -> ps_outfile s <> Some (pc_rfile p) ->
      implMG RNG (Pcap.pcap_ng_cleanup MOps PR p) s
        (fun u s' RNG' ms' => fp_le RNG RNG' /\ exists B Af FB1 FB2, FB = FB1 ++ (pc_rfile p, Af, FILE_BLOCK) :: FB2
           /\ cleanup_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CLc FB1 FB2 lo P B Af p m (ps_outfile s) u s' RNG' ms')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (pk_cleanup_ng PK)) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition pcap_close_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CLc PB FB : list cblk) (FL : list fblock) (trC : list Z) (lo P : Z) (p : pcapT),
      SPOA L RNG sp tp s (CLc ++ PB) FB FL lo PCAP_L4_STACK m ->
      ucallerA (depth_pcap_close) L m sp s0 ra trC -> traces_pcap_close TP L (bv_unsigned ra) trC -> nofr (frames_pcap_close) FL -> PCRC P p PB FB m -> a0 = Z_to_bv 64 P -> ps_outfile s <> Some (pc_rfile p) ->
      implMG RNG (Pcap.pcap_close MOps PR p) s
        (pcap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CLc lo m
           (fun _ s' a0v m' PB' FB' => ps_outfile s' = ps_outfile s /\ PB' = [] /\ exists F1 F2 Af, FB = F1 ++ (pc_rfile p, Af, FILE_BLOCK) :: F2 /\ FB' = F1 ++ F2))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_CLOSE_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition open_common_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (FL : list fblock) (CL FB : list cblk) (lo EB total : Z) (ej : list byte) (m : mem) (o : option hptr) : ((list Z) + hptr) -> PS -> footprint -> machine_state -> Prop :=
    fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ ps_outfile s' = o /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256)) m m'
      /\ match r with
         | inl msg => exists junk', a0v = Z_to_bv 64 0 /\ GIO L RNG' s' CL FB FL m'
             /\ rw_cells asegs m' EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk']
             /\ Z.of_nat (length msg) < 256 /\ Forall (fun z => 0 < z < 256) msg
         | inr q => exists P, a0v = Z_to_bv 64 P /\ GIO L RNG' s' ((q, P, total) :: CL) FB FL m'
             /\ rw_cells asegs m' P ([CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 (-1)); CB 28 (repeat (Z_to_bv 8 0) 28);
                                     C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); CB 128 (repeat (Z_to_bv 8 0) 128); C4 (Z_to_bv 64 (-1));
                                     CB (Z.to_nat (total - 188)) (repeat (Z_to_bv 8 0) (Z.to_nat (total - 188)))])
             /\ rw_cells asegs m' EB [CB 256 ej]
         end.
  Definition open_offline_common_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (trC : list Z) (lo EB total : Z) (ej : list byte),
      SPOA L RNG sp tp s CL FB FL lo PCAP_L1B_STACK m ->
      ucallerA (depth_open_offline_common) L m sp s0 ra trC -> traces_open_offline_common TP L (bv_unsigned ra) trC -> nofr (frames_open_offline_common) FL ->
      a0 = Z_to_bv 64 EB -> a1 = Z_to_bv 64 total -> a2 = Z_to_bv 64 PCAP_PRIV_OFF -> (total = PCAP_SF_TOTAL \/ total = PCAP_NG_SF_TOTAL) ->
      rw_cells asegs m EB [CB 256 ej] -> cobjA RNG m FL CL EB 256 -> EB mod 8 = 0 ->
      implMG RNG (Pcap.pcapint_open_offline_common MOps PR total) s
        (open_common_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo EB total ej m (ps_outfile s))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_OPEN_OFFLINE_COMMON_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition check_header_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (FL : list fblock) (CL FB : list cblk) (lo MG EB ERR : Z) (magic : list Z) (f : hptr) (m : mem) (o : option hptr) : check_result -> PS -> footprint -> machine_state -> Prop :=
    fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m' errw, hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ ps_outfile s' = o /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4)) m m'
      /\ rw_cells asegs m' MG [CB 4 (map b8 magic)] /\ rw_cells asegs m' ERR [C4 errw]
      /\ match r with
         | CH_NotMe => a0v = Z_to_bv 64 0 /\ errw = Z_to_bv 64 0 /\ GIO L RNG' s' CL FB FL m' /\ exists e, rw_cells asegs m' EB [CB 256 e]
         | CH_Err msg => exists junk', a0v = Z_to_bv 64 0 /\ errw = Z_to_bv 64 1 /\ GIO L RNG' s' CL FB FL m'
             /\ rw_cells asegs m' EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk'] /\ Z.of_nat (length msg) < 256
             /\ Forall (fun z => 0 < z < 256) msg
         | CH_Ok p => exists P PB, a0v = Z_to_bv 64 P /\ GIO L RNG' s' (CL ++ PB) FB FL m' /\ pre_PCAPR (hptr:=hptr) P p PB m' /\ pc_rfile p = f
             /\ (exists e, rw_cells asegs m' EB [CB 256 e])
         end.

  (* [comment removed for export] *)
  Definition check_header_stmt_for (ng : bool) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (trC : list Z) (lo MG FA EB ERR : Z) (f : hptr)
           (magic : list Z) (ej : list byte) (ec : cell) (fuel : nat),
      SPOA L RNG sp tp s CL FB FL lo PCAP_L2_STACK m ->
      ucallerA (depth_check_header ng) L m sp s0 ra trC -> traces_check_header TP ng L (bv_unsigned ra) trC -> nofr (frames_check_header ng) FL -> In (f, FA, FILE_BLOCK) FB ->
      a0 = Z_to_bv 64 MG -> a1 = Z_to_bv 64 FA -> a2 = Z_to_bv 64 0 (* [comment removed for export] *) -> a3 = Z_to_bv 64 EB -> a4 = Z_to_bv 64 ERR ->
      rw_cells asegs m MG [CB 4 (map b8 magic)] -> Forall (fun z => 0 <= z < 256) magic -> length magic = 4%nat ->
      rw_cells asegs m EB [CB 256 ej] -> rw_cells asegs m ERR [ec] -> csize ec = 4%nat ->
      cobjA RNG m FL CL MG 4 -> cobjA RNG m FL CL ERR 4 -> (MG + 4 <= ERR \/ ERR + 4 <= MG) ->   (* [comment removed for export] *)
      cobjA RNG m FL CL EB 256 -> (EB + 256 <= ERR \/ ERR + 4 <= EB) -> (EB + 256 <= MG \/ MG + 4 <= EB) -> ERR mod 4 = 0 -> EB mod 8 = 0 ->
      implMG RNG ((if ng then Pcap.pcap_ng_check_header MOps PR fuel else Pcap.pcap_check_header MOps PR) magic f 0) s
        (check_header_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m (ps_outfile s))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (if ng then PCAP_NG_CHECK_HEADER_ENTRY else PCAP_CHECK_HEADER_ENTRY)) fc None m (seg_rom asegs)).
  Definition pcap_check_header_stmt : Prop := check_header_stmt_for false.      (* [comment removed for export] *)
  Definition pcap_ng_check_header_stmt : Prop := check_header_stmt_for true.    (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition open_result_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (FL : list fblock) (CL : list cblk) (lo EB : Z) (m : mem) (o : option hptr)
      (keepFB : list cblk -> Prop)   (* [comment removed for export] *)
      (okFB : list cblk -> pcapT -> Prop)
      : ((list Z) + pcapT) -> PS -> footprint -> machine_state -> Prop :=
    fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m' FB', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ ps_outfile s' = o /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256)) m m'
      /\ match r with
         | inl msg => exists junk', a0v = Z_to_bv 64 0 /\ keepFB FB' /\ GIO L RNG' s' CL FB' FL m'
             /\ rw_cells asegs m' EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk'] /\ Z.of_nat (length msg) < 256
             /\ Forall (fun z => 0 < z < 256) msg
         | inr p => exists P PB, a0v = Z_to_bv 64 P /\ okFB FB' p /\ GIO L RNG' s' (CL ++ PB) FB' FL m' /\ PCR P p PB FB' m'
             /\ (exists e, rw_cells asegs m' EB [CB 256 e])
         end.

  Definition fopen_offline_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (trC : list Z) (lo FA EB : Z) (f : hptr) (ej : list byte) (fuel : nat),
      SPOA L RNG sp tp s CL FB FL lo PCAP_L3_STACK m ->
      ucallerA (depth_fopen_offline) L m sp s0 ra trC -> traces_fopen_offline TP L (bv_unsigned ra) trC -> nofr (frames_fopen_offline) FL -> In (f, FA, FILE_BLOCK) FB ->
      a0 = Z_to_bv 64 FA -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 EB ->
      rw_cells asegs m EB [CB 256 ej] -> cobjA RNG m FL CL EB 256 -> EB mod 8 = 0 ->
      implMG RNG (Pcap.pcap_fopen_offline_with_tstamp_precision MOps PR fuel f 0) s
        (open_result_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL lo EB m (ps_outfile s)
           (fun FB' => FB' = FB) (fun FB' p => FB' = FB /\ pc_rfile p = f))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_FOPEN_OFFLINE_WTP_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition open_offline_stmt_at (ENTRY : Z) (a_err : word -> word -> word) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (trC : list Z) (lo NAME EB : Z) (name slack ej : list byte) (fuel : nat),
      SPOA L RNG sp tp s CL FB FL lo PCAP_L4_STACK m ->
      ucallerA (depth_open_offline ENTRY) L m sp s0 ra trC -> traces_open_offline TP ENTRY L (bv_unsigned ra) trC -> nofr (frames_open_offline ENTRY) FL ->
      a0 = Z_to_bv 64 NAME -> a_err a1 a2 = Z_to_bv 64 EB -> (ENTRY = PCAP_OPEN_OFFLINE_WTP_ENTRY -> a1 = Z_to_bv 64 0) ->
      bytes_at asegs m NAME (name ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) name -> (1 <= length name <= 4095)%nat ->
      nth_error name 0 <> Some (Z_to_bv 8 45) ->
      open_name_ok false name ->   (* [comment removed for export] *)
      (- (NAME + Z.of_nat (length name) + 1)) mod 8 <= Z.of_nat (length slack) ->
      cobjA RNG m FL CL NAME (Z.of_nat (length name) + 1) -> clocA FL CL NAME (Z.of_nat (length name) + 1 + Z.of_nat (length slack)) -> rng RNG NAME (Z.of_nat (length name) + 1 + Z.of_nat (length slack)) ->   (* [comment removed for export] *)
      rw_cells asegs m EB [CB 256 ej] -> cobjA RNG m FL CL EB 256 -> EB mod 8 = 0 ->
      (NAME + Z.of_nat (length name) + 1 + Z.of_nat (length slack) <= EB \/ EB + 256 <= NAME) ->
      implMG RNG (Pcap.pcap_open_offline MOps PR fuel (map bv_unsigned name)) s
        (open_result_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL lo EB m (ps_outfile s)
           (fun FB' => FB' = FB) (fun FB' p => exists FA, FB' = (pc_rfile p, FA, FILE_BLOCK) :: FB))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ENTRY) fc None m (seg_rom asegs)).
  Definition pcap_open_offline_stmt : Prop := open_offline_stmt_at PCAP_OPEN_OFFLINE_ENTRY (fun a1 _ => a1).
  Definition pcap_open_offline_wtp_stmt : Prop := open_offline_stmt_at PCAP_OPEN_OFFLINE_WTP_ENTRY (fun _ a2 => a2).

  (* [comment removed for export] *)
End Ifaces.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MALLOC_ENTRY : Z := 0x561e0.   (* [comment removed for export] *)
Definition CALLOC_ENTRY : Z := 0x561e4.   (* [comment removed for export] *)
Definition REALLOC_ENTRY : Z := 0x561e8.  (* [comment removed for export] *)
Definition FREE_ENTRY : Z := 0x561dc.     (* [comment removed for export] *)
Definition FOPEN_ENTRY : Z := 0x4453c.    (* [comment removed for export] *)
Definition FCLOSE_ENTRY : Z := 0x44544.
Definition FREAD_ENTRY : Z := 0x444f4.
Definition VSNPRINTF_ENTRY : Z := 0x4450c.
Definition SNPRINTF_ENTRY : Z := 0x44518.
Definition STRERROR_R_ENTRY : Z := 0x4452c.
Definition STRLEN_ENTRY : Z := 0x444d0.
Definition FPRINTF_ENTRY : Z := 0x44514.
Definition PRINTF_ENTRY : Z := 0x44510.
Definition FWRITE_ENTRY : Z := 0x444f8.
Definition MEMCPY_ENTRY : Z := 0x549cc.   (* [comment removed for export] *)
Definition MEMSET_ENTRY : Z := 0x54e68.   (* [comment removed for export] *)
Definition FERROR_ENTRY : Z := 0x9a6b0.   (* [comment removed for export] *)
Definition FILENO_ENTRY : Z := 0x9ab3c.
Definition ERRNO_LOCATION_ENTRY : Z := 0x9489c.
Definition REMOVE_ENTRY : Z := 0x9b134.
Definition UNLINK_ENTRY : Z := 0xa42c0.
Definition CLOSE_ENTRY : Z := 0xa41ac.
Definition MKSTEMP_ENTRY : Z := 0x8e0a8.  (* [comment removed for export] *)
Definition STACK_MALLOC_0 : Z := 0x3f2e0. (* [comment removed for export] *)
Definition STACK_MALLOC_1 : Z := 0x3f454. (* [comment removed for export] *)
Definition STACK_MALLOC_7 : Z := 0x3f5e4. (* [comment removed for export] *)
Definition STACK_FREE_7 : Z := 0x3f760.   (* [comment removed for export] *)
Definition SET_SHADOW_00 : Z := 0x582d0.  (* [comment removed for export] *)
Definition SET_SHADOW_F8 : Z := 0x583f0.
Definition STDIN_FILE : Z := 0xa9f80.     (* [comment removed for export] *)
Definition STDIN_P : Z := 0xa5788.        (* [comment removed for export] *)
Definition GOT_STDIN : Z := 0xa6538.      (* [comment removed for export] *)
Definition GOT_SHBASE : Z := 0xa5890.     (* [comment removed for export] *)
Definition GOT_MEMSET : Z := 0xa58b0.     (* [comment removed for export] *)
Definition GOT_UAR : Z := 0xa58e8.        (* [comment removed for export] *)
Definition STR_RB : Z := 0x212e0.         (* [comment removed for export] *)
Definition STR_PERCENT_S : Z := 0x21300.  (* [comment removed for export] *)
Definition STR_PERCENT_S_FMT : Z := 0x217a0. (* [comment removed for export] *)
Definition STR_STATS_NA : Z := 0x215a0.   (* [comment removed for export] *)
Definition STR_MALLOC : Z := 0x21640.     (* [comment removed for export] *)

Definition OUTFILE_ADDR : Z := 0x5e1080.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition MALLOC_STACK : Z := 4096.
Definition REALLOC_STACK : Z := 8192.     (* [comment removed for export] *)
Definition FREE_STACK : Z := 4096.
Definition FAKE_STACK : Z := 4096.        (* [comment removed for export] *)
Definition STDIO_STACK : Z := 0x4000.
Definition PCAP_L0_STACK : Z := 0x6000.   (* [comment removed for export] *)
Definition PCAP_L1_STACK : Z := 0x8000.   (* [comment removed for export] *)
Definition PCAP_L1B_STACK : Z := 0xa000.  (* [comment removed for export] *)
Definition PCAP_L2_STACK : Z := 0xe000.   (* [comment removed for export] *)
Definition PCAP_L3_STACK : Z := 0x10000.  (* [comment removed for export] *)
Definition PCAP_L4_STACK : Z := 0x12000.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition open_name_ok (wr : bool) (name : list byte) : Prop :=
  if wr then (Namei.path_has_slash name = false \/ name = Uapi.devnull_path)
  else (Namei.path_has_slash name = false /\ Fs.path_eqb name Namei.dotdot_path = false).

(* [comment removed for export] *)
Notation rng_aimg_sh RNG := (rng RNG 0x7fffa000 780288).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ff_class (f : fframe) : Z :=
  match f with
  | FF_FOPEN_OFFLINE | FF_FMT_ERRMSG | FF_NG_CHECK_HEADER | FF_READ_BLOCK => 0
  | FF_CHECK_HEADER | FF_OFFLINE_READ | FF_NEXT_EX => 1
  | FF_NEXT_PACKET | FF_FUZZ_ONE_INPUT => 7
  end.
Definition ff_size (f : fframe) : Z := 64 * 2 ^ ff_class f.
(* [comment removed for export] *)
Definition site_frameA (site : stack_site) : option (fframe * Z) :=
  match site with
  | SiteMagic => Some (FF_FOPEN_OFFLINE, 32)
  | SitePcapHdrRest => Some (FF_CHECK_HEADER, 36)
  | SiteSfHdr => Some (FF_NEXT_PACKET, 32)
  | SiteDiscardBuf => Some (FF_NEXT_PACKET, 96)
  | SiteNgTotalLength => Some (FF_NG_CHECK_HEADER, 32)
  | SiteNgByteOrderMagic => Some (FF_NG_CHECK_HEADER, 48)
  | SiteBhdrCheckHeader | SiteBhdrNextPacket => Some (FF_READ_BLOCK, 32)
  | SiteReadStage => None
  end.

Section Ifaces.
  Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  #[local] Abbreviation MP := (Monad.M (PState H hptr)).
  #[local] Abbreviation pcapT := (PcapTypes.pcap hptr hptr).
  #[local] Abbreviation PR := (prims HO FO sites).
  #[local] Abbreviation PCR := (@PCAPR hptr).
  #[local] Abbreviation PCRC := (@PCAPR_closable hptr).

  (* [comment removed for export] *)
  Variable GIOA : alayout -> footprint -> PS -> list cblk -> list cblk -> list fblock -> mem -> Prop.
  (* [comment removed for export] *)
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation GIO := GIOA.

  (* [comment removed for export] *)
  Definition iv_in_frames (FL : list fblock) (iv : Z * Z) : Prop :=
    Exists (fun fr => fb_addr fr <= fst iv /\ snd iv <= fb_addr fr + fb_size fr) FL.
  Definition iv_in_frame_shadow (FL : list fblock) (iv : Z * Z) : Prop :=
    Exists (fun fr => Z.shiftr (fb_addr fr) 3 + 2147450880 <= fst iv /\ snd iv <= Z.shiftr (fb_addr fr) 3 + 2147450880 + Z.shiftr (fb_size fr) 3) FL.
  Definition client_ivA (FL : list fblock) (CL : list cblk) (iv : Z * Z) : Prop :=
    ATOP + 4096 <= fst iv \/ iv_in_block CL iv \/ iv_in_frames FL iv \/ iv_in_frame_shadow FL iv.
  Definition pcap_iv (FL : list fblock) (PB : list cblk) (iv : Z * Z) : Prop := client_ivA FL PB iv.

  Record gia_laws : Prop := mkGL {
    (* [comment removed for export] *)
    gl_block : forall L RNG s CL FB FL m b, GIOA L RNG s CL FB FL m -> In b (CL ++ FB) -> blockA RNG m b;
    gl_apart : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m -> blocks_apart (CL ++ FB);
    (* [comment removed for export] *)
    gl_frames : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m -> Forall (frameA RNG m) FL /\ List.NoDup (map fb_fn FL);
    gl_fr_apart : forall L RNG s CL FB FL m a, GIOA L RNG s CL FB FL m -> in_frames FL a -> ~ in_block (CL ++ FB) a;
    gl_fr_disj : forall L RNG s CL FB FL m fr1 fr2, GIOA L RNG s CL FB FL m -> In fr1 FL -> In fr2 FL -> fb_fn fr1 <> fb_fn fr2 ->
                 fb_addr fr1 + fb_size fr1 <= fb_addr fr2 \/ fb_addr fr2 + fb_size fr2 <= fb_addr fr1;
    gl_site : forall L RNG s CL FB FL m f Fb n site off, GIOA L RNG s CL FB FL m -> In (f, Fb, n) FL ->
                 site_frameA site = Some (f, off) -> fo_site FO s site = Some (Fb + off);
    gl_flag : forall L RNG s CL FB FL m f Fb n, GIOA L RNG s CL FB FL m -> In (f, Fb, n) FL ->
                 rw_cells asegs m (fflagA L f Fb) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflagA L f Fb) 1
                 /\ ablk (fflagA L f Fb) (fflagA L f Fb + 1) /\ fflagA L f Fb + 1 <= ATOP
                 /\ ~ in_block (CL ++ FB) (fflagA L f Fb) /\ ~ in_frames FL (fflagA L f Fb);
    (* [comment removed for export] *)
    gl_client_frame : forall L RNG s CL FB FL m m' W, GIOA L RNG s CL FB FL m -> munch W m m' -> wmono asegs m m' ->
                 Forall (client_ivA FL CL) W -> GIOA L RNG s CL FB FL m';
    gl_frame : forall L RNG s CLc PB FB FL m m' W, GIOA L RNG s (CLc ++ PB) FB FL m -> munch W m m' -> wmono asegs m m' ->
                 Forall (pcap_iv FL PB) W -> GIOA L RNG s (CLc ++ PB) FB FL m';
    gl_keeps : forall L RNG s CLc PB FB FLc FLo m m' W SP, GIOA L RNG s (CLc ++ PB) FB (FLo ++ FLc) m -> munch W m m' -> wmono asegs m m' ->
                 Forall (fun iv => (ATOP + 4096 <= fst iv /\ snd iv <= SP) \/ iv_in_block PB iv \/ iv_in_frames FLo iv \/ iv_in_frame_shadow FLo iv) W ->
                 ATOP + 4096 <= SP -> agrees_on (client_keeps FLc CLc SP) m m';
    (* [comment removed for export] *)
    gl_keepsx : forall L RNG s CLc PB FB FLc FLo m m' W WX SP, GIOA L RNG s (CLc ++ PB) FB (FLo ++ FLc) m -> munch (W ++ WX) m m' -> wmono asegs m m' ->
                 Forall (fun iv => (ATOP + 4096 <= fst iv /\ snd iv <= SP) \/ iv_in_block PB iv \/ iv_in_frames FLo iv \/ iv_in_frame_shadow FLo iv) W ->
                 ATOP + 4096 <= SP -> agrees_on (fun a => client_keeps FLc CLc SP a /\ outside WX a) m m';
    (* [comment removed for export] *)
    gl_rt : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m ->
                 artcells m /\ rw_cells asegs m GOT_UAR [C8 (Z_to_bv 64 0xaea00)];
    (* [comment removed for export] *)
    gl_globals : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m ->
                 wr_at asegs m 0x7fffa000 780288 /\ Forall (fun g => unpoisoned m (fst g) (fst g + snd g)) client_globals;
    (* [comment removed for export] *)
    gl_tls : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m -> rng_atls RNG -> mobjA RNG m (ATP + -200) 504;
    (* [comment removed for export] *)
    gl_tls_apart : forall L RNG s CL FB FL m a, GIOA L RNG s CL FB FL m -> in_block (CL ++ FB) a \/ in_frames FL a ->
                 ~ (ATP + -200 <= a < ATP + -200 + 504);
    (* [comment removed for export] *)
    gl_stdin : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m ->
                 rw_cells asegs m GOT_STDIN [C8 (Z_to_bv 64 STDIN_P)] /\ rw_cells asegs m STDIN_P [C8 (Z_to_bv 64 STDIN_FILE)]
                 /\ unpoisoned m STDIN_P (STDIN_P + 8);
    (* [comment removed for export] *)
    gl_stack : forall L RNG s CL FB FL m A n, GIOA L RNG s CL FB FL m -> ATOP + 4096 <= A -> 0 <= n -> A + n <= al_top L ->
                 unpoisoned m A (A + n) /\ arenaA RNG m A n;
    (* [comment removed for export] *)
    gl_got_memset : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m -> rw_cells asegs m GOT_MEMSET [C8 (Z_to_bv 64 0xa7740)]
  }.

  (* [comment removed for export] *)
  Definition gia_addr_law : Prop :=
    forall L RNG s CL FB FL m b, GIOA L RNG s CL FB FL m -> In b (CL ++ FB) -> blk_addr HO s (cb_tok b) = cb_addr b.
  (* [comment removed for export] *)
  Definition gia_perm_law : Prop :=
    forall L RNG s CL CL' FB FL m, GIOA L RNG s CL FB FL m -> Permutation.Permutation CL CL' -> GIOA L RNG s CL' FB FL m.
  (* [comment removed for export] *)
  Record gia_harn_laws : Prop := mkGH {
    gh_outfile : forall L RNG s CL FB FL m, GIOA L RNG s CL FB FL m ->
                 match ps_outfile s with
                 | None => rw_cells asegs m OUTFILE_ADDR [C8 (Z_to_bv 64 0)]
                 | Some q => exists A, In (q, A, FILE_BLOCK) FB /\ rw_cells asegs m OUTFILE_ADDR [C8 (Z_to_bv 64 A)]
                 end;
    (* [comment removed for export] *)
    gh_set_outfile : forall L RNG s CL FB FL m m' (o : option hptr), GIOA L RNG s CL FB FL m -> ps_outfile s = None ->
                 match o with
                 | None => rw_cells asegs m' OUTFILE_ADDR [C8 (Z_to_bv 64 0)]
                 | Some q => exists A, In (q, A, FILE_BLOCK) FB /\ rw_cells asegs m' OUTFILE_ADDR [C8 (Z_to_bv 64 A)]
                 end ->
                 munch [(OUTFILE_ADDR, OUTFILE_ADDR + 8)] m m' -> wmono asegs m m' ->
                 GIOA L RNG (set_outfile o s) CL FB FL m'
  }.

  (* [comment removed for export] *)
  #[using="Type"] Lemma gia_in_block_below : forall (GL : gia_laws) L RNG s CL FB FL m a, GIOA L RNG s CL FB FL m -> in_block (CL ++ FB) a -> 0 < a < ATOP.
  Proof.
    intros GL L RNG s CL FB FL m a G Hin. apply in_block_In in Hin as (b & Hb & Hr).
    destruct (gl_block GL _ _ _ _ _ _ _ _ G Hb) as ((_ & _ & T & _) & P0 & _). lia.
  Qed.
  #[using="Type"] Lemma gia_in_frames_below : forall (GL : gia_laws) L RNG s CL FB FL m a, GIOA L RNG s CL FB FL m -> in_frames FL a -> 0 < a < ATOP.
  Proof.
    intros GL L RNG s CL FB FL m a G Hin. apply in_frames_In in Hin as (fr & Hf & Hr).
    destruct (gl_frames GL _ _ _ _ _ _ _ G) as [FA _]. pose proof (proj1 (Forall_forall _ _) FA fr Hf) as (BAND & T & _).
    unfold ablk, AIMG_HI in BAND. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma gia_in_frame_sh_band : forall (GL : gia_laws) L RNG s CL FB FL m a, GIOA L RNG s CL FB FL m -> in_frame_sh FL a -> 0x7fff7000 <= a < 0x10007fff8000.
  Proof.
    intros GL L RNG s CL FB FL m a G Hin. apply in_frame_sh_In in Hin as (fr & Hf & Hr).
    destruct (gl_frames GL _ _ _ _ _ _ _ G) as [FA _]. pose proof (proj1 (Forall_forall _ _) FA fr Hf) as (BAND & T & A64 & N64 & _).
    rewrite !Z.shiftr_div_pow2 in Hr by lia. change (2 ^ 3) with 8 in Hr.
    unfold ablk, AIMG_HI, KLS in BAND. atop_facts. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma gia_global_unp : forall (GL : gia_laws) L RNG s CL FB FL m A n, GIOA L RNG s CL FB FL m -> In (A, n) client_globals -> unpoisoned m A (A + n).
  Proof.
    intros GL L RNG s CL FB FL m A n G Hin. destruct (gl_globals GL _ _ _ _ _ _ _ G) as [_ FA].
    exact (proj1 (Forall_forall _ _) FA (A, n) Hin).
  Qed.
  Definition gia_global_mobjA__stmt : Prop := forall (GL : gia_laws) L RNG s CL FB FL m A n, GIOA L RNG s CL FB FL m -> In (A, n) client_globals ->
    rng_aimg RNG -> rng_aimg_sh RNG -> mobjA RNG m A n.
  Section Sz5.
  Variables L RNG s CL FB FL m A n : ltac2:(SecDiet.SzSec.tyM 'gia_global_mobjA__stmt "hvvvvvvvvv" @L).
  #[using="Type"] Lemma gia_global_mobjA__body : ltac2:(SecDiet.SzSec.bodyP 'gia_global_mobjA__stmt "hvvvvvvvvv").
  Proof.
    intros GL G Hin RI RS.
 pose proof (gia_global_unp GL _ _ _ _ _ _ _ _ _ G Hin) as U.
    destruct (gl_globals GL _ _ _ _ _ _ _ G) as [W _].
    assert (B : 0x10040 <= A /\ A + n <= 0x603fc0 /\ 0 <= n).
    { clear - Hin. unfold client_globals in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin. }
    destruct B as (B1 & B2 & B3). apply static_mobjA; assumption.
  Qed.
  End Sz5.
  #[using="Type"] Lemma gia_global_mobjA : ltac:(let t := eval cbv delta [gia_global_mobjA__stmt] in gia_global_mobjA__stmt in exact t).
  Proof. intros GL L RNG s CL FB FL m A n. ltac2:(SecDiet.SzSec.closeP 'gia_global_mobjA__body "hvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma gia_stack_sobjA : forall (GL : gia_laws) L RNG s CL FB FL m lo SP A n, GIOA L RNG s CL FB FL m ->
    ATOP + 4096 <= lo -> lo <= SP -> SP <= A -> 0 <= n -> A + n <= al_top L -> rng RNG lo (al_top L - lo) -> sobjA L RNG m SP A n.
  Proof.
    intros GL L RNG s CL FB FL m lo SP A n G LO LS SA Hn HT RS. atop_facts.
    destruct (gl_stack GL _ _ _ _ _ _ _ A n G ltac:(lia) Hn HT) as [U AR].
    split; [exact SA|]. split; [exact HT|]. split; [exact U|]. split; [eapply rng_sub'; [exact RS| lia]|].
    eapply arenaA_sh_rng; [exact AR| lia| exact Hn].
  Qed.
  #[using="Type"] Lemma gia_stack_mobjA : forall (GL : gia_laws) L RNG s CL FB FL m lo A n, GIOA L RNG s CL FB FL m ->
    ATOP + 4096 <= lo -> lo <= A -> 0 <= n -> A + n + 8 <= al_top L -> al_top L <= 2^47 -> rng RNG lo (al_top L - lo) -> mobjA RNG m A n.
  Proof.
    intros GL L RNG s CL FB FL m lo A n G LO LA Hn HT T47 RS. atop_facts.
    destruct (gl_stack GL _ _ _ _ _ _ _ A n G ltac:(lia) Hn ltac:(lia)) as [U AR].
    split; [lia|]. split; [lia|]. split; [exact U|]. split; [eapply rng_sub'; [exact RS| lia]|]. split; [exact AR|].
    unfold app_blk, KHIGH, KEND. split; [lia|]. right. lia.
  Qed.

  #[using="Type"] Lemma gia_global_robjA : forall (GL : gia_laws) L RNG s CL FB FL m A n, GIOA L RNG s CL FB FL m -> In (A, n) client_globals -> A + n <= 0x32000 ->
    rng_aimg RNG -> rng_aimg_sh RNG -> robjA RNG m FL CL A n.
  Proof.
    intros GL L RNG s CL FB FL m A n G Hin HR RI RS. split; [|eapply gia_global_mobjA; eassumption].
    right. exists (A, n). cbn [fst snd]. split; [exact Hin|]. split; [lia|]. split; [lia| exact HR].
  Qed.

  (* [comment removed for export] *)
  Definition std_pre_o (L : alayout) (RNG : footprint) (sp tp : word) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo budget : Z) (m : mem) : Prop :=
    GIOA L RNG s CL FB FL m /\ stk asegs m lo (bv_unsigned sp) /\ ATOP + 4096 <= lo /\ lo + budget <= bv_unsigned sp
    /\ (bv_unsigned sp + 16 < al_top L /\ al_top L <= 2^47) /\ mem_inv asegs m /\ tp = Z_to_bv 64 ATP /\ bv_unsigned sp mod 16 = 0
    /\ (rng RNG lo (al_top L - lo) /\ rng_aimg RNG /\ rng_aimg_sh RNG /\ rng_atls RNG).
  #[local] Abbreviation SPOA := std_pre_o.

  Definition hpost_regs (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (a0v : word) (m' : mem) (ms' : machine_state) : Prop :=
    exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition malloc_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo n : Z),
      SPOA L RNG sp tp s CL FB FL lo MALLOC_STACK m -> a0 = Z_to_bv 64 n -> 1 <= n < 2^29 - 2^16 ->
      unw_okA L RNG m lo AMALLOC_PC sp s0 ra ->
      implMG RNG (pmalloc HO n) s
        (fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ match r with
              | None => False
              | Some q => exists A junk, a0v = Z_to_bv 64 A /\ GIO L RNG' s' ((q, A, n) :: CL) FB FL m'
                          /\ rw_cells asegs m' A [CB (Z.to_nat n) junk]
              end)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 MALLOC_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition calloc_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo cnt sz : Z),
      SPOA L RNG sp tp s CL FB FL lo MALLOC_STACK m -> a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 sz -> 0 <= cnt < 2^32 -> 0 <= sz < 2^32 -> 1 <= cnt * sz <= 3260 ->
      unw_okA L RNG m lo (tp_cpc TP) sp s0 ra ->
      implMG RNG (pcalloc HO cnt sz) s
        (fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ match r with
              | None => False
              | Some q => exists A, a0v = Z_to_bv 64 A /\ GIO L RNG' s' ((q, A, cnt * sz) :: CL) FB FL m'
                          /\ rw_cells asegs m' A [CB (Z.to_nat (cnt * sz)) (repeat (Z_to_bv 8 0) (Z.to_nat (cnt * sz)))]
              end)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 CALLOC_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition realloc_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (C1 C2 FB : list cblk) (FL : list fblock) (q : hptr) (A sz lo n : Z) (bs : list byte),
      SPOA L RNG sp tp s (C1 ++ (q, A, sz) :: C2) FB FL lo REALLOC_STACK m -> a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 1 <= n < 2^29 - 2^16 ->
      rw_cells asegs m A [CB (Z.to_nat sz) bs] ->
      unw_okA L RNG m lo (tp_rpc TP) sp s0 ra ->
      implMG RNG (prealloc HO q n) s
        (fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL (C1 ++ C2) (bv_unsigned sp)) m m'
           /\ match r with
              | None => False
              | Some q' => exists A' junk, a0v = Z_to_bv 64 A' /\ GIO L RNG' s' ((q', A', n) :: C1 ++ C2) FB FL m'
                          /\ rw_cells asegs m' A' [CB (Z.to_nat (Z.min sz n)) (firstn (Z.to_nat (Z.min sz n)) bs); CB (Z.to_nat (n - Z.min sz n)) junk]
              end)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 REALLOC_ENTRY) fc None m (seg_rom asegs)).

  Definition free_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (C1 C2 FB : list cblk) (FL : list fblock) (q : hptr) (A n lo : Z),
      SPOA L RNG sp tp s (C1 ++ (q, A, n) :: C2) FB FL lo FREE_STACK m -> a0 = Z_to_bv 64 A ->
      unw_okA L RNG m lo AFREE_PC sp s0 ra ->
      implMG RNG (pfree HO q) s
        (fun _ s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL (C1 ++ C2) (bv_unsigned sp)) m m'
           /\ GIO L RNG' s' (C1 ++ C2) FB FL m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREE_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition free_null_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo : Z),
      SPOA L RNG sp tp s CL FB FL lo FREE_STACK m -> a0 = Z_to_bv 64 0 ->
      unw_okA L RNG m lo AFREE_PC sp s0 ra ->
      evtF asegs RNG (fun ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ GIO L RNG s CL FB FL m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREE_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition fenter_stmt_o (k SYM : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo req : Z)
           (f : fframe) (A : Type) (body : MP A) (Q : A -> PS -> footprint -> machine_state -> Prop),
      SPOA L RNG sp tp s CL FB FL lo FAKE_STACK m -> a0 = Z_to_bv 64 req -> 0 < req <= ff_size f ->
      ~ In f (map fb_fn FL) -> ff_class f = k ->
      (forall (Fb : Z) (s' : PS) (m' : mem) (j0 j1 j2 : word) (junk : list byte) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
         GIO L RNG s' CL FB ((f, Fb, ff_size f) :: FL) m' ->
         ps_outfile s' = ps_outfile s -> ps_libc s' = ps_libc s -> ps_tls s' = ps_tls s ->
         mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp) -> agrees_on (client_keeps FL CL (bv_unsigned sp)) m m' ->
         0 < Fb -> length junk = Z.to_nat (ff_size f - 32) ->
         rw_cells asegs m' Fb [C8 j0; C8 j1; C8 j2; CB (Z.to_nat (ff_size f - 32)) junk; C8 (Z_to_bv 64 (fflagA L f Fb))] ->
         rw_cells asegs m' (Z.shiftr Fb 3 + 2147450880) [CB (Z.to_nat (ff_size f / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (ff_size f / 8)))] ->
         implMG RNG body s' Q
           (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 Fb) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom asegs))) ->
      implMG RNG (fo_enter FO _ f body) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 SYM) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition fenter7_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo req : Z)
           (f : fframe) (A : Type) (body : MP A) (Q : A -> PS -> footprint -> machine_state -> Prop),
      SPOA L RNG sp tp s CL FB FL lo FAKE_STACK m -> a0 = Z_to_bv 64 req -> 0 < req <= ff_size f -> req mod 8 = 0 ->
      ~ In f (map fb_fn FL) -> ff_class f = 7 ->
      (forall (Fb : Z) (s' : PS) (m' : mem) (j0 j1 j2 : word) (junk sjunk : list byte) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
         GIO L RNG s' CL FB ((f, Fb, ff_size f) :: FL) m' ->
         ps_outfile s' = ps_outfile s -> ps_libc s' = ps_libc s -> ps_tls s' = ps_tls s ->
         mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp) -> agrees_on (client_keeps FL CL (bv_unsigned sp)) m m' ->
         0 < Fb -> length junk = Z.to_nat (ff_size f - 32) -> length sjunk = Z.to_nat ((ff_size f - req) / 8) ->
         rw_cells asegs m' Fb [C8 j0; C8 j1; C8 j2; CB (Z.to_nat (ff_size f - 32)) junk; C8 (Z_to_bv 64 (fflagA L f Fb))] ->
         rw_cells asegs m' (Z.shiftr Fb 3 + 2147450880)
           [CB (Z.to_nat (req / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (req / 8))); CB (Z.to_nat ((ff_size f - req) / 8)) sjunk] ->
         implMG RNG body s' Q
           (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 Fb) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom asegs))) ->
      implMG RNG (fo_enter FO _ f body) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 STACK_MALLOC_7) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition fret_inline_law : Prop :=
    forall (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (f : fframe) (Fb : Z) (m m' : mem)
           (A : Type) (x : A) (Q : A -> PS -> footprint -> machine_state -> Prop) (ms : machine_state),
      GIO L RNG s CL FB ((f, Fb, ff_size f) :: FL) m -> ff_class f <= 6 ->
      munch [(fflagA L f Fb, fflagA L f Fb + 1)] m m' -> wmono asegs m m' -> rw_cells asegs m' (fflagA L f Fb) [C1 (Z_to_bv 8 0)] ->
      (forall s' : PS, GIO L RNG s' CL FB FL m' -> ps_outfile s' = ps_outfile s -> ps_libc s' = ps_libc s -> ps_tls s' = ps_tls s ->
         evtF asegs RNG (Q x s' RNG) ms) ->
      implMG RNG (fo_ret FO _ f x) s Q ms.

  (* [comment removed for export] *)
  Definition ffree7_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo Fb req : Z)
           (f : fframe) (A : Type) (x : A) (Q : A -> PS -> footprint -> machine_state -> Prop),
      SPOA L RNG sp tp s CL FB ((f, Fb, ff_size f) :: FL) lo FAKE_STACK m -> ff_class f = 7 ->
      a0 = Z_to_bv 64 Fb -> a1 = Z_to_bv 64 req -> 0 < req <= ff_size f -> req mod 8 = 0 ->
      rw_cells asegs m (Fb + ff_size f - 8) [C8 (Z_to_bv 64 (fflagA L f Fb))] ->
      (forall (s' : PS) (m' : mem) (a0' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
         GIO L RNG s' CL FB FL m' -> ps_outfile s' = ps_outfile s -> ps_libc s' = ps_libc s -> ps_tls s' = ps_tls s ->
         mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp) -> agrees_on (client_keeps FL CL (bv_unsigned sp)) m m' ->
         evtF asegs RNG (Q x s' RNG)
           (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom asegs))) ->
      implMG RNG (fo_ret FO _ f x) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 STACK_FREE_7) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition set_shadow_stmt (SYM v : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (RNG : footprint) (lo SA n : Z) (old : list byte),
      mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo + FAKE_STACK <= bv_unsigned sp -> ATOP + 4096 <= lo ->
      artcells m -> rw_cells asegs m GOT_MEMSET [C8 (Z_to_bv 64 0xa7740)] ->   (* [comment removed for export] *)
      a0 = Z_to_bv 64 SA -> a1 = Z_to_bv 64 n -> 0 < SA -> 0 < n <= 4096 ->
      rw_cells asegs m SA [CB (Z.to_nat n) old] -> rng RNG SA n -> rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG ->
      evtF asegs RNG (fun ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ munch [(bv_unsigned sp - FAKE_STACK, bv_unsigned sp); (SA, SA + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
           /\ stk asegs m' lo (bv_unsigned sp)
           /\ rw_cells asegs m' SA [CB (Z.to_nat n) (repeat (Z_to_bv 8 v) (Z.to_nat n))])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 SYM) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition strlen_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo P : Z) (bs slack : list byte),
      SPOA L RNG sp tp s CL FB FL lo STDIO_STACK m -> a0 = Z_to_bv 64 P ->
      bytes_at asegs m P (bs ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) bs -> Z.of_nat (length bs) < 2^24 ->
      (- (P + Z.of_nat (length bs) + 1)) mod 8 <= Z.of_nat (length slack) ->
      robjA RNG m FL CL P (Z.of_nat (length bs) + 1) -> rng RNG P (Z.of_nat (length bs) + 1 + Z.of_nat (length slack)) ->
      evtF asegs RNG (fun ms' => exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ munch [(bv_unsigned sp - STDIO_STACK, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
           /\ stk asegs m' lo (bv_unsigned sp)
           /\ a0v = Z_to_bv 64 (Z.of_nat (length bs)))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 STRLEN_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition PCAP_TLS_ERRBUF : Z := 20.
  Definition strerror_r_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo e : Z),
      SPOA L RNG sp tp s CL FB FL lo STDIO_STACK m ->
      a0 = Z_to_bv 64 (s32 e) -> a1 = Z_to_bv 64 (ATP + PCAP_TLS_ERRBUF) -> a2 = Z_to_bv 64 256 -> -2^31 <= e < 2^31 ->
      evtF asegs RNG (fun ms' => exists a0v m' rest, hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ a0v = Z_to_bv 64 0
           /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ GIO L RNG s CL FB FL m'
           /\ rw_cells asegs m' (ATP + PCAP_TLS_ERRBUF) [CB (length (Fmt.strerror e) + 1) (map (fun z => Z_to_bv 8 z) (Fmt.strerror e) ++ [Z_to_bv 8 0]);
                                                         CB (255 - length (Fmt.strerror e)) rest])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 STRERROR_R_ENTRY) fc None m (seg_rom asegs)).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition mode_ok (wr : bool) (md : list byte) : Prop :=
    if wr then (md = [Z_to_bv 8 119] \/ md = [Z_to_bv 8 119; Z_to_bv 8 98])     (* [comment removed for export] *)
    else (md = [Z_to_bv 8 114] \/ md = [Z_to_bv 8 114; Z_to_bv 8 98]).          (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition mode_lit (wr : bool) (MODE : Z) (md : list byte) : Prop :=
    if wr then (MODE = 0x21020 /\ md = [Z_to_bv 8 119]) \/ (MODE = 0x211a0 /\ md = [Z_to_bv 8 119; Z_to_bv 8 98])   (* [comment removed for export] *)
    else (MODE = STR_RB /\ md = [Z_to_bv 8 114; Z_to_bv 8 98]).                                                  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition fopen_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (trC : list Z) (lo NAME MODE : Z) (name md : list byte) (wr : bool),
      SPOA L RNG sp tp s CL FB FL lo STDIO_STACK m ->
      ucallerA 0%nat L m sp s0 ra trC -> tp_fopen TP L (bv_unsigned ra) trC -> a0 = Z_to_bv 64 NAME -> a1 = Z_to_bv 64 MODE ->
      bytes_at asegs m NAME (name ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) name -> (1 <= length name <= 4095)%nat ->
      open_name_ok wr name ->   (* [comment removed for export] *)
      robjA RNG m FL CL NAME (Z.of_nat (length name) + 1) ->
      bytes_at asegs m MODE (md ++ [Z_to_bv 8 0]) -> mode_lit wr MODE md -> robjA RNG m FL CL MODE (Z.of_nat (length md) + 1) ->
      implMG RNG (s_fopen HO (map bv_unsigned name) wr) s
        (fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ match r with
              | None => a0v = Z_to_bv 64 0 /\ GIO L RNG' s' CL FB FL m'
                        /\ rw_cells asegs m' (ATP + -164) [C4 (Z_to_bv 64 (lc_errno (ps_libc s')))]   (* [comment removed for export] *)
                        /\ 0 <= lc_errno (ps_libc s') < 2^31
              | Some f => exists Af, a0v = Z_to_bv 64 Af /\ GIO L RNG' s' CL ((f, Af, FILE_BLOCK) :: FB) FL m'
              end)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FOPEN_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition fclose_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL F1 F2 : list cblk) (FL : list fblock) (trC : list Z) (f : hptr) (Af lo : Z),
      SPOA L RNG sp tp s CL (F1 ++ (f, Af, FILE_BLOCK) :: F2) FL lo STDIO_STACK m ->
      ucallerA 0%nat L m sp s0 ra trC -> tp_fclose TP L (bv_unsigned ra) trC -> a0 = Z_to_bv 64 Af -> ps_outfile s <> Some f ->
      implMG RNG (s_fclose HO f) s
        (fun _ s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ GIO L RNG' s' CL (F1 ++ F2) FL m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FCLOSE_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition fread_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (f : hptr) (Af D n lo : Z) (junk : list byte),
      SPOA L RNG sp tp s CL FB FL lo STDIO_STACK m -> In (f, Af, FILE_BLOCK) FB ->
      a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 n -> a3 = Z_to_bv 64 Af -> 0 <= n <= 2^30 ->
      rw_cells asegs m D [CB (Z.to_nat n) junk] -> cobjA RNG m FL CL D n ->
      implMG RNG (s_fread HO f D n) s
        (fun got s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m' junk', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
           /\ agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ ~ (D <= a < D + n)) m m'
           /\ GIO L RNG' s' CL FB FL m'
           /\ a0v = Z_to_bv 64 (zlength got) /\ 0 <= zlength got <= n /\ Forall (fun z => 0 <= z < 256) got
           /\ rw_cells asegs m' D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junk'])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREAD_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition ferror_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (f : hptr) (Af lo : Z),
      SPOA L RNG sp tp s CL FB FL lo STDIO_STACK m -> In (f, Af, FILE_BLOCK) FB -> a0 = Z_to_bv 64 Af ->
      implMG RNG (s_ferror HO f) s
        (fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ GIO L RNG' s' CL FB FL m' /\ s' = s /\ a0v = Z_to_bv 64 (Z.b2z r)
           (* [comment removed for export] *)
           /\ (r = true -> rw_cells asegs m' (ATP + -164) [C4 (Z_to_bv 64 (lc_errno (ps_libc s')))] /\ 0 <= lc_errno (ps_libc s') < 2^31))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FERROR_ENTRY) fc None m (seg_rom asegs)).

  Definition fileno_stmt_o : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (f : hptr) (Af lo : Z),
      SPOA L RNG sp tp s CL FB FL lo STDIO_STACK m -> In (f, Af, FILE_BLOCK) FB -> a0 = Z_to_bv 64 Af ->
      implMG RNG (s_fileno HO f) s
        (fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ GIO L RNG' s' CL FB FL m' /\ s' = s /\ a0v = Z_to_bv 64 r /\ 0 <= r < 2^31)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FILENO_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition fprintf_dd_stmt_o (FMT : Z) (mk : Z -> Z -> list (list Z)) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (f : hptr) (Af lo v1 v2 : Z),
      SPOA L RNG sp tp s CL FB FL lo STDIO_STACK m -> In (f, Af, FILE_BLOCK) FB ->
      a0 = Z_to_bv 64 Af -> a1 = Z_to_bv 64 FMT -> a2 = sx32 (Z_to_bv 64 v1) -> a3 = sx32 (Z_to_bv 64 v2) -> 0 <= v1 < 2^32 -> 0 <= v2 < 2^32 ->
      implMG RNG (s_fprintf HO f (mk v1 v2)) s
        (fun _ s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ GIO L RNG' s' CL FB FL m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FPRINTF_ENTRY) fc None m (seg_rom asegs)).

  Definition fprintf_s_stmt_o (FMT : Z) (mk : list Z -> list (list Z)) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (f : hptr) (Af lo P : Z) (str slack : list byte),
      SPOA L RNG sp tp s CL FB FL lo STDIO_STACK m -> In (f, Af, FILE_BLOCK) FB ->
      a0 = Z_to_bv 64 Af -> a1 = Z_to_bv 64 FMT -> a2 = Z_to_bv 64 P ->
      bytes_at asegs m P (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) < 2^24 ->
      (- (P + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->   (* [comment removed for export] *)
      cobjA RNG m FL CL P (Z.of_nat (length str) + 1 + Z.of_nat (length slack)) ->   (* [comment removed for export] *)
      Z.of_nat (length slack) <= 2^24 ->   (* [comment removed for export] *)
      implMG RNG (s_fprintf HO f (mk (map bv_unsigned str))) s
        (fun _ s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
           /\ GIO L RNG' s' CL FB FL m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FPRINTF_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition fmt_at (m : mem) (FMTA : Z) (fs : string) : Prop :=
    bytes_at asegs m FMTA (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string fs) ++ [Z_to_bv 8 0])
    /\ 0x10000 <= FMTA /\ FMTA + Z.of_nat (String.length fs) + 1 <= 0x32000
    /\ In (FMTA, Z.of_nat (String.length fs) + 1) client_globals.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition conv_ok (c : conv) (a : farg) : bool :=
    match c, a with
    | Cs, AStr _ => true
    | Cd, AInt _ => true | Cu, AInt _ => true | Czu, AInt _ => true | C08x, AInt _ => true
    | _, _ => false
    end.
  Fixpoint items_ok (its : list fitem) (args : list farg) : bool :=
    match its with
    | [] => match args with [] => true | _ => false end
    | FLit l :: its' => forallb (fun c => negb (c =? 0) && negb (c =? 37)) l && items_ok its' args
    | FConv c :: its' => match args with a :: args' => conv_ok c a && items_ok its' args' | [] => false end
    | FBad _ :: _ => false
    end.
  Definition fmt_ok (fs : string) (args : list farg) : bool :=
    items_ok (fmt fs) args && (Z.of_nat (String.length fs) <? 4096).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition slocA (tls : bool) (FL : list fblock) (CL : list cblk) (P n k : Z) : Prop :=
    clocA FL CL P (n + k)
    \/ (exists g, In g client_globals /\ fst g <= P /\ P + n <= fst g + snd g /\ fst g + snd g <= 0x32000 /\ P + n + k <= 0x32000)
    \/ (tls = true /\ ATP + -200 <= P /\ P + n + k <= ATP + -200 + 504).
  Definition farg_word (tls : bool) (L : alayout) (RNG : footprint) (FL : list fblock) (CL : list cblk) (SP D dn : Z) (m : mem) (a : farg) (w : word) : Prop :=
    match a with
    | AInt z => w = Z_to_bv 64 z
    | AStr cs => exists P bs slack, w = Z_to_bv 64 P /\ bytes_at asegs m P (bs ++ Z_to_bv 8 0 :: slack) /\ ~ In (Z_to_bv 8 0) bs
                 /\ cs = map bv_unsigned bs /\ Z.of_nat (length bs) < 2^24
                 /\ (- (P + Z.of_nat (length bs) + 1)) mod 8 <= Z.of_nat (length slack)
                 /\ (P + Z.of_nat (length bs) + 1 + Z.of_nat (length slack) <= D \/ D + dn <= P)
                 (* [comment removed for export] *)
                 /\ slocA tls FL CL P (Z.of_nat (length bs) + 1) (Z.of_nat (length slack))
                 /\ mobjA RNG m P (Z.of_nat (length bs) + 1)
                 /\ rng RNG P (Z.of_nat (length bs) + 1 + Z.of_nat (length slack))
    end.

  (* [comment removed for export] *)
  Definition snprintf_spec_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo DST n FMTA : Z) (fs : string) (args : list farg) (junk : list byte),
      SPOA L RNG sp tp s CL FB FL lo STDIO_STACK m ->
      a0 = Z_to_bv 64 DST -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 FMTA -> 1 <= n < 2^31 -> fmt_at m FMTA fs -> fmt_ok fs args = true ->
      (length args <= 3)%nat -> Forall2 (farg_word true L RNG FL CL (bv_unsigned sp) DST n m) args (firstn (length args) [a3; a4; a5]) ->
      rw_cells asegs m DST [CB (Z.to_nat n) junk] -> cobjA RNG m FL CL DST n ->
      evtF asegs RNG (fun ms' => exists a0v m' junk', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ munch [(bv_unsigned sp - STDIO_STACK, bv_unsigned sp); (DST, DST + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
           /\ stk asegs m' lo (bv_unsigned sp)
           /\ a0v = Z_to_bv 64 (snprintf_ret (fmt fs) args)
           /\ rw_cells asegs m' DST [CB (length (Fmt.snprintf n fs args) + 1) (map b8 (Fmt.snprintf n fs args) ++ [Z_to_bv 8 0]);
                                   CB (Z.to_nat n - length (Fmt.snprintf n fs args) - 1) junk'])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 SNPRINTF_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition vsnprintf_spec_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo DST n FMTA AP : Z) (fs : string) (args : list farg)
           (ws : list word) (junk : list byte),
      SPOA L RNG sp tp s CL FB FL lo STDIO_STACK m ->
      a0 = Z_to_bv 64 DST -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 FMTA -> a3 = Z_to_bv 64 AP -> 1 <= n < 2^31 -> fmt_at m FMTA fs -> fmt_ok fs args = true ->
      length ws = length args -> (length args <= 4)%nat -> Forall2 (farg_word true L RNG FL CL (bv_unsigned sp) DST n m) args ws ->
      rw_cells asegs m AP (map C8 ws) -> bv_unsigned sp <= AP -> AP + 8 * Z.of_nat (length ws) <= al_top L ->
      (AP + 8 * Z.of_nat (length ws) <= DST \/ DST + n <= AP) ->
      rw_cells asegs m DST [CB (Z.to_nat n) junk] -> cobjA RNG m FL CL DST n ->
      evtF asegs RNG (fun ms' => exists a0v m' junk', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ munch [(bv_unsigned sp - STDIO_STACK, bv_unsigned sp); (DST, DST + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
           /\ stk asegs m' lo (bv_unsigned sp)
           /\ a0v = Z_to_bv 64 (snprintf_ret (fmt fs) args)
           /\ rw_cells asegs m' DST [CB (length (Fmt.snprintf n fs args) + 1) (map b8 (Fmt.snprintf n fs args) ++ [Z_to_bv 8 0]);
                                   CB (Z.to_nat n - length (Fmt.snprintf n fs args) - 1) junk'])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 VSNPRINTF_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition leaf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (v : word) (fr lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - fr, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ a0 = v.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition LT_TABLE : Z := 0x22000.
  Definition linktype_to_dlt_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (RNG : footprint) (lo lt : Z),
      mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp -> ATOP + 4096 <= lo ->
      artcells m -> unpoisoned m LT_TABLE (LT_TABLE + 28) ->
      rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng_aimg_sh RNG ->
      a0 = Z_to_bv 64 lt -> 0 <= lt < 2^32 ->
      evtF asegs RNG (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 (linktype_to_dlt lt)) 16 lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 LINKTYPE_TO_DLT_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition max_snaplen_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (RNG : footprint) (lo dlt : Z),
      mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) ->
      a0 = Z_to_bv 64 dlt -> 0 <= dlt < 2^64 ->
      evtF asegs RNG (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 (max_snaplen_for_dlt dlt)) 0 lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 MAX_SNAPLEN_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition adjust_snapshot_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (RNG : footprint) (lo lt snaplen : Z),
      mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) ->
      a0 = Z_to_bv 64 lt -> 0 <= lt < 2^31 -> a1 = Z_to_bv 64 (s32 snaplen) -> 0 <= snaplen < 2^32 ->
      evtF asegs RNG (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 (pcapint_adjust_snapshot lt snaplen)) 0 lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_ADJUST_SNAPSHOT_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ONESHOT_STACK : Z := 32 + 0x2000.
  Definition oneshot_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (RNG : footprint) (lo U HD PKT SRC : Z) (pd w0 w1 w2 o0 o1 o2 : word) (pkc : cell),
      a0 = Z_to_bv 64 U -> a1 = Z_to_bv 64 SRC ->
      rw_cells asegs m U [C8 (Z_to_bv 64 HD); C8 (Z_to_bv 64 PKT); C8 pd] ->
      rw_cells asegs m SRC [C8 w0; C8 w1; C8 w2] ->
      rw_cells asegs m HD [C8 o0; C8 o1; C8 o2] ->
      rw_cells asegs m PKT [pkc] -> csize pkc = 8%nat ->
      (HD + 24 <= U \/ U + 24 <= HD) -> (HD + 24 <= SRC \/ SRC + 24 <= HD) -> (HD + 24 <= PKT \/ PKT + 8 <= HD) ->
      (PKT + 8 <= U \/ U + 24 <= PKT) -> (PKT + 8 <= SRC \/ SRC + 24 <= PKT) ->
      mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo + ONESHOT_STACK <= bv_unsigned sp -> ATOP + 4096 <= lo ->
      artcells m ->
      aobjA RNG m U 24 -> aobjA RNG m SRC 24 -> aobjA RNG m HD 24 -> aobjA RNG m PKT 8 ->
      U + 24 <= ATOP -> SRC + 24 <= ATOP -> HD + 24 <= ATOP -> PKT + 8 <= ATOP ->
      U mod 8 = 0 -> PKT mod 8 = 0 -> HD mod 8 = 0 -> SRC mod 8 = 0 ->
      rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_atls RNG ->
      evtF asegs RNG (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
          ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (ret_pc ra) fc None m' (seg_rom asegs)
          /\ munch [(bv_unsigned sp - ONESHOT_STACK, bv_unsigned sp); (HD, HD + 24); (PKT, PKT + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
          /\ stk asegs m' lo (bv_unsigned sp)
          /\ rw_cells asegs m' U [C8 (Z_to_bv 64 HD); C8 (Z_to_bv 64 PKT); C8 pd]
          /\ rw_cells asegs m' SRC [C8 w0; C8 w1; C8 w2]
          /\ rw_cells asegs m' HD [C8 w0; C8 w1; C8 w2]
          /\ rw_cells asegs m' PKT [C8 a2])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (pk_oneshot PK)) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition pcap_strerror_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo e : Z),
      SPOA L RNG sp tp s CL FB FL lo PCAP_L0_STACK m ->
      a0 = Z_to_bv 64 (s32 e) -> -2^31 <= e < 2^31 ->
      evtF asegs RNG (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' rest,
          ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (ATP + PCAP_TLS_ERRBUF)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (ret_pc ra) fc None m' (seg_rom asegs)
          /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CL (bv_unsigned sp)) m m'
          /\ GIO L RNG s CL FB FL m'
          /\ rw_cells asegs m' (ATP + PCAP_TLS_ERRBUF) [CB (length (Fmt.strerror e) + 1) (map b8 (Fmt.strerror e) ++ [Z_to_bv 8 0]);
                                                        CB (255 - length (Fmt.strerror e)) rest])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_STRERROR_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition fmt_errmsg_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (lo EB FMTA e : Z) (fs : string) (args : list farg)
           (junk : list byte),
      SPOA L RNG sp tp s CL FB FL lo PCAP_L1_STACK m -> ~ In FF_FMT_ERRMSG (map fb_fn FL) ->
      a0 = Z_to_bv 64 EB -> a1 = Z_to_bv 64 256 -> a2 = Z_to_bv 64 (s32 e) -> -2^31 <= e < 2^31 -> a3 = Z_to_bv 64 FMTA ->
      fmt_at m FMTA fs -> fmt_ok fs args = true -> (length args <= 1)%nat -> Forall2 (farg_word false L RNG FL CL (bv_unsigned sp) EB 256 m) args (firstn (length args) [a4]) ->
      rw_cells asegs m EB [CB 256 junk] -> cobjA RNG m FL CL EB 256 -> EB mod 8 = 0 ->
      implMG RNG (fo_enter FO _ FF_FMT_ERRMSG (fo_ret FO _ FF_FMT_ERRMSG (fmt_errmsg fs args e))) s
        (fun r s' RNG' ms' => fp_le RNG RNG' /\ r = fmt_errmsg fs args e /\
          exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' junk',
          ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (ret_pc ra) fc None m' (seg_rom asegs)
          /\ ps_outfile s' = ps_outfile s /\ ps_libc s' = ps_libc s /\ ps_tls s' = ps_tls s
          /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
          /\ agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256)) m m'
          /\ GIO L RNG' s' CL FB FL m'
          /\ rw_cells asegs m' EB [CB (length (fmt_errmsg fs args e) + 1) (map b8 (fmt_errmsg fs args e) ++ [Z_to_bv 8 0]);
                                  CB (255 - length (fmt_errmsg fs args e)) junk'])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_FMT_ERRMSG_ENTRY) fc None m (seg_rom asegs)).

  Definition pcap_post {A} (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (FL : list fblock) (CLc : list cblk) (lo : Z) (m : mem)
      (X : A -> PS -> word -> mem -> list cblk -> list cblk -> Prop) : A -> PS -> footprint -> machine_state -> Prop :=
    fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m' PB' FB', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CLc (bv_unsigned sp)) m m'
      /\ GIO L RNG' s' (CLc ++ PB') FB' FL m' /\ X r s' a0v m' PB' FB'.

  (* [comment removed for export] *)
  Definition pcap_stats_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CLc PB FB : list cblk) (FL : list fblock) (trC : list Z) (lo P : Z) (p : pcapT),
      SPOA L RNG sp tp s (CLc ++ PB) FB FL lo PCAP_L1_STACK m ->
      ucallerA (depth_pcap_stats) L m sp s0 ra trC -> traces_pcap_stats TP L (bv_unsigned ra) trC -> nofr (frames_pcap_stats) FL -> PCRC P p PB FB m -> a0 = Z_to_bv 64 P ->
      implMG RNG (Pcap.pcap_stats MOps p) s
        (pcap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CLc lo m
           (fun r s' a0v m' PB' FB' => PB' = PB /\ FB' = FB /\ s' = s /\ a0v = Z_to_bv 64 (fst r) /\ fst r = -1 /\ PCRC P (snd r) PB FB m'))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_STATS_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition next_packet_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (FL : list fblock) (CLc : list cblk) (FB : list cblk) (lo P HA DA : Z) (m : mem) (o : option hptr) : (Z * pkthdr * pcapT) -> PS -> footprint -> machine_state -> Prop :=
    fun r s' RNG' ms' => fp_le RNG RNG' /\ let '(st, h, p') := r in
      exists a0v m' PB' (dw : cell), hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ ps_outfile s' = o /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8)) m m'
      /\ GIO L RNG' s' (CLc ++ PB') FB FL m' /\ (st <> -1 -> PCR P p' PB' FB m') /\ (st = -1 -> PCRC P p' PB' FB m')
      /\ a0v = Z_to_bv 64 st /\ (st = 1 \/ st = 0 \/ st = -1)
      /\ (st = 1 -> rw_cells asegs m' HA (hdr_cells h) /\ 0 <= h_caplen h < 2^32 /\ 0 <= h_len h < 2^32)
      /\ (st <> 1 -> exists hcs', cells_size hcs' = 24%nat /\ rw_cells asegs m' HA hcs')
      /\ rw_cells asegs m' DA [dw] /\ csize dw = 8%nat.

  Definition next_packet_op_stmt_for (ng : bool) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CLc PB FB : list cblk) (FL : list fblock) (trC : list Z) (lo P HA DA : Z) (p : pcapT) (fuel : nat)
           (hcs : list cell) (dc : cell),
      SPOA L RNG sp tp s (CLc ++ PB) FB FL lo PCAP_L2_STACK m ->
      ucallerA (depth_next_packet_op ng) L m sp s0 ra trC -> traces_next_packet_op TP ng L (bv_unsigned ra) trC -> nofr (frames_next_packet_op ng) FL -> PCR P p PB FB m -> is_ng p = ng -> bv_unsigned sp + 16 <= bv_unsigned s0 ->   (* [comment removed for export] *)
     
      a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 HA -> a2 = Z_to_bv 64 DA ->
      rw_cells asegs m HA hcs -> cells_size hcs = 24%nat -> rw_cells asegs m DA [dc] -> csize dc = 8%nat ->
      cobjA RNG m FL CLc HA 24 -> cobjA RNG m FL CLc DA 8 -> (HA + 24 <= DA \/ DA + 8 <= HA) ->   (* [comment removed for export] *) HA mod 8 = 0 -> DA mod 8 = 0 ->
      implMG RNG (next_packet_op MOps PR fuel p) s
        (next_packet_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CLc FB lo P HA DA m (ps_outfile s))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (np_entry p)) fc None m (seg_rom asegs)).
  Definition pcap_next_packet_stmt : Prop := next_packet_op_stmt_for false.
  Definition pcap_ng_next_packet_stmt : Prop := next_packet_op_stmt_for true.

  (* [comment removed for export] *)
  Definition offline_read_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CLc PB FB : list cblk) (FL : list fblock) (trC : list Z) (lo P U PKT : Z) (p : pcapT) (fuel : nat)
           (pd : word) (pkc : cell),
      SPOA L RNG sp tp s (CLc ++ PB) FB FL lo PCAP_L3_STACK m ->
      ucallerA (depth_offline_read) L m sp s0 ra trC -> traces_offline_read TP L (bv_unsigned ra) trC -> nofr (frames_offline_read) FL -> PCR P p PB FB m ->
      a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 (pk_oneshot PK) -> a3 = Z_to_bv 64 U ->
      rw_cells asegs m U [C8 (Z_to_bv 64 (P + PCAP_HDR_OFF)); C8 (Z_to_bv 64 PKT); C8 pd] -> rw_cells asegs m PKT [pkc] -> csize pkc = 8%nat ->
      cobjA RNG m FL CLc U 24 -> cobjA RNG m FL CLc PKT 8 -> (U + 24 <= PKT \/ PKT + 8 <= U) ->
      U mod 8 = 0 -> PKT mod 8 = 0 ->
      implMG RNG (pcapint_offline_read_1 MOps PR fuel p) s
        (fun r s' RNG' ms' => fp_le RNG RNG' /\ let '(st, p') := r in
           exists a0v m' PB' (pk' : cell), hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
           /\ agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (PKT <= a < PKT + 8)) m m'
           /\ GIO L RNG' s' (CLc ++ PB') FB FL m' /\ (st <> -1 -> PCR P p' PB' FB m') /\ (st = -1 -> PCRC P p' PB' FB m')
           /\ a0v = Z_to_bv 64 st /\ (st = 1 \/ st = 0 \/ st = -1)
           /\ rw_cells asegs m' U [C8 (Z_to_bv 64 (P + PCAP_HDR_OFF)); C8 (Z_to_bv 64 PKT); C8 pd]
           /\ rw_cells asegs m' PKT [pk'] /\ csize pk' = 8%nat)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_OFFLINE_READ_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition pcap_next_ex_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CLc PB FB : list cblk) (FL : list fblock) (trC : list Z) (lo P HP PKT : Z) (p : pcapT) (fuel : nat)
           (hc pkc : cell),
      SPOA L RNG sp tp s (CLc ++ PB) FB FL lo PCAP_L4_STACK m ->
      ucallerA (depth_pcap_next_ex) L m sp s0 ra trC -> traces_pcap_next_ex TP L (bv_unsigned ra) trC -> nofr (frames_pcap_next_ex) FL -> PCR P p PB FB m ->
      a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 HP -> a2 = Z_to_bv 64 PKT ->
      rw_cells asegs m HP [hc] -> csize hc = 8%nat -> rw_cells asegs m PKT [pkc] -> csize pkc = 8%nat ->
      cobjA RNG m FL CLc HP 8 -> cobjA RNG m FL CLc PKT 8 -> (HP + 8 <= PKT \/ PKT + 8 <= HP) ->
      HP mod 8 = 0 -> PKT mod 8 = 0 ->
      implMG RNG (Pcap.pcap_next_ex MOps PR fuel p) s
        (fun r s' RNG' ms' => fp_le RNG RNG' /\ let '(st, p') := r in
           exists a0v m' PB' (pk' : cell), hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
           /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
           /\ agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HP <= a < HP + 8) /\ ~ (PKT <= a < PKT + 8)) m m'
           /\ GIO L RNG' s' (CLc ++ PB') FB FL m' /\ (st <> -1 -> PCR P p' PB' FB m') /\ (st = -1 -> PCRC P p' PB' FB m')
           /\ a0v = Z_to_bv 64 st /\ (st = 1 \/ st = -2 \/ st = -1)
           /\ rw_cells asegs m' HP [C8 (Z_to_bv 64 (P + PCAP_HDR_OFF))]
           /\ rw_cells asegs m' PKT [pk'] /\ csize pk' = 8%nat)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_NEXT_EX_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition cleanup_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (FL : list fblock) (CLc FB1 FB2 : list cblk) (lo P B Af : Z) (p : pcapT) (m : mem) (o : option hptr) : unit -> PS -> footprint -> machine_state -> Prop :=
    fun _ s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m' j', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ ps_outfile s' = o /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ agrees_on (client_keeps FL CLc (bv_unsigned sp)) m m'
      /\ GIO L RNG' s' (CLc ++ [(pc_self p, P, psize p)]) (FB1 ++ FB2) FL m'
      /\ rw_cells asegs m' P (pcap_cells p P B Af j').

  Definition sf_cleanup_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CLc FB1 FB2 : list cblk) (FL : list fblock) (trC : list Z) (lo P B Af : Z) (p : pcapT) (j : pcap_junk),
      SPOA L RNG sp tp s (CLc ++ [(pc_self p, P, psize p); (pc_buffer p, B, pc_bufalloc p)]) (FB1 ++ (pc_rfile p, Af, FILE_BLOCK) :: FB2) FL lo PCAP_L3_STACK m ->
      ucallerA (depth_sf_cleanup) L m sp s0 ra trC -> traces_sf_cleanup TP L (bv_unsigned ra) trC -> nofr (frames_sf_cleanup) FL ->
      rw_cells asegs m P (pcap_cells p P B Af j) -> a0 = Z_to_bv 64 P -> ps_outfile s <> Some (pc_rfile p) ->
      implMG RNG (Pcap.pcapint_sf_cleanup MOps PR p) s
        (cleanup_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CLc FB1 FB2 lo P B Af p m (ps_outfile s))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (pk_cleanup_sf PK)) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition ng_cleanup_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CLc PB FB : list cblk) (FL : list fblock) (trC : list Z) (lo P : Z) (p : pcapT),
      SPOA L RNG sp tp s (CLc ++ PB) FB FL lo PCAP_L3_STACK m ->
      ucallerA (depth_ng_cleanup) L m sp s0 ra trC -> traces_ng_cleanup TP L (bv_unsigned ra) trC -> nofr (frames_ng_cleanup) FL -> PCRC P p PB FB m -> is_ng p = true ->
      a0 = Z_to_bv 64 P -> ps_outfile s <> Some (pc_rfile p) ->
      implMG RNG (Pcap.pcap_ng_cleanup MOps PR p) s
        (fun u s' RNG' ms' => fp_le RNG RNG' /\ exists B Af FB1 FB2, FB = FB1 ++ (pc_rfile p, Af, FILE_BLOCK) :: FB2
           /\ cleanup_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CLc FB1 FB2 lo P B Af p m (ps_outfile s) u s' RNG' ms')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (pk_cleanup_ng PK)) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition pcap_close_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CLc PB FB : list cblk) (FL : list fblock) (trC : list Z) (lo P : Z) (p : pcapT),
      SPOA L RNG sp tp s (CLc ++ PB) FB FL lo PCAP_L4_STACK m ->
      ucallerA (depth_pcap_close) L m sp s0 ra trC -> traces_pcap_close TP L (bv_unsigned ra) trC -> nofr (frames_pcap_close) FL -> PCRC P p PB FB m -> a0 = Z_to_bv 64 P -> ps_outfile s <> Some (pc_rfile p) ->
      implMG RNG (Pcap.pcap_close MOps PR p) s
        (pcap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CLc lo m
           (fun _ s' a0v m' PB' FB' => ps_outfile s' = ps_outfile s /\ PB' = [] /\ exists F1 F2 Af, FB = F1 ++ (pc_rfile p, Af, FILE_BLOCK) :: F2 /\ FB' = F1 ++ F2))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_CLOSE_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition open_common_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (FL : list fblock) (CL FB : list cblk) (lo EB total : Z) (ej : list byte) (m : mem) (o : option hptr) : ((list Z) + hptr) -> PS -> footprint -> machine_state -> Prop :=
    fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ ps_outfile s' = o /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256)) m m'
      /\ match r with
         | inl msg => exists junk', a0v = Z_to_bv 64 0 /\ GIO L RNG' s' CL FB FL m'
             /\ rw_cells asegs m' EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk']
             /\ Z.of_nat (length msg) < 256 /\ Forall (fun z => 0 < z < 256) msg
         | inr q => exists P, a0v = Z_to_bv 64 P /\ GIO L RNG' s' ((q, P, total) :: CL) FB FL m'
             /\ rw_cells asegs m' P ([CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 (-1)); CB 28 (repeat (Z_to_bv 8 0) 28);
                                     C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); CB 128 (repeat (Z_to_bv 8 0) 128); C4 (Z_to_bv 64 (-1));
                                     CB (Z.to_nat (total - 188)) (repeat (Z_to_bv 8 0) (Z.to_nat (total - 188)))])
             /\ rw_cells asegs m' EB [CB 256 ej]
         end.
  Definition open_offline_common_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (trC : list Z) (lo EB total : Z) (ej : list byte),
      SPOA L RNG sp tp s CL FB FL lo PCAP_L1B_STACK m ->
      ucallerA (depth_open_offline_common) L m sp s0 ra trC -> traces_open_offline_common TP L (bv_unsigned ra) trC -> nofr (frames_open_offline_common) FL ->
      bv_unsigned sp + 16 <= bv_unsigned s0 ->   (* [comment removed for export] *)
      a0 = Z_to_bv 64 EB -> a1 = Z_to_bv 64 total -> a2 = Z_to_bv 64 PCAP_PRIV_OFF -> (total = PCAP_SF_TOTAL \/ total = PCAP_NG_SF_TOTAL) ->
      rw_cells asegs m EB [CB 256 ej] -> cobjA RNG m FL CL EB 256 -> EB mod 8 = 0 ->
      implMG RNG (Pcap.pcapint_open_offline_common MOps PR total) s
        (open_common_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo EB total ej m (ps_outfile s))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_OPEN_OFFLINE_COMMON_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition check_header_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (FL : list fblock) (CL FB : list cblk) (lo MG EB ERR : Z) (magic : list Z) (f : hptr) (m : mem) (o : option hptr) : check_result -> PS -> footprint -> machine_state -> Prop :=
    fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m' errw, hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ ps_outfile s' = o /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256) /\ ~ (ERR <= a < ERR + 4)) m m'
      /\ rw_cells asegs m' MG [CB 4 (map b8 magic)] /\ rw_cells asegs m' ERR [C4 errw]
      /\ match r with
         | CH_NotMe => a0v = Z_to_bv 64 0 /\ errw = Z_to_bv 64 0 /\ GIO L RNG' s' CL FB FL m' /\ exists e, rw_cells asegs m' EB [CB 256 e]
         | CH_Err msg => exists junk', a0v = Z_to_bv 64 0 /\ errw = Z_to_bv 64 1 /\ GIO L RNG' s' CL FB FL m'
             /\ rw_cells asegs m' EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk'] /\ Z.of_nat (length msg) < 256
             /\ Forall (fun z => 0 < z < 256) msg
         | CH_Ok p => exists P PB, a0v = Z_to_bv 64 P /\ GIO L RNG' s' (CL ++ PB) FB FL m' /\ pre_PCAPR (hptr:=hptr) P p PB m' /\ pc_rfile p = f
             /\ (exists e, rw_cells asegs m' EB [CB 256 e])
         end.

  (* [comment removed for export] *)
  Definition check_header_stmt_for (ng : bool) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (trC : list Z) (lo MG FA EB ERR : Z) (f : hptr)
           (magic : list Z) (ej : list byte) (ec : cell) (fuel : nat),
      SPOA L RNG sp tp s CL FB FL lo PCAP_L2_STACK m ->
      ucallerA (depth_check_header ng) L m sp s0 ra trC -> traces_check_header TP ng L (bv_unsigned ra) trC -> nofr (frames_check_header ng) FL -> In (f, FA, FILE_BLOCK) FB ->
      a0 = Z_to_bv 64 MG -> a1 = Z_to_bv 64 FA -> a2 = Z_to_bv 64 0 (* [comment removed for export] *) -> a3 = Z_to_bv 64 EB -> a4 = Z_to_bv 64 ERR ->
      rw_cells asegs m MG [CB 4 (map b8 magic)] -> Forall (fun z => 0 <= z < 256) magic -> length magic = 4%nat ->
      rw_cells asegs m EB [CB 256 ej] -> rw_cells asegs m ERR [ec] -> csize ec = 4%nat ->
      cobjA RNG m FL CL MG 4 -> cobjA RNG m FL CL ERR 4 -> (MG + 4 <= ERR \/ ERR + 4 <= MG) ->   (* [comment removed for export] *)
      cobjA RNG m FL CL EB 256 -> (EB + 256 <= ERR \/ ERR + 4 <= EB) -> (EB + 256 <= MG \/ MG + 4 <= EB) -> ERR mod 4 = 0 -> EB mod 8 = 0 ->
      implMG RNG ((if ng then Pcap.pcap_ng_check_header MOps PR fuel else Pcap.pcap_check_header MOps PR) magic f 0) s
        (check_header_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL FB lo MG EB ERR magic f m (ps_outfile s))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (if ng then PCAP_NG_CHECK_HEADER_ENTRY else PCAP_CHECK_HEADER_ENTRY)) fc None m (seg_rom asegs)).
  Definition pcap_check_header_stmt : Prop := check_header_stmt_for false.      (* [comment removed for export] *)
  Definition pcap_ng_check_header_stmt : Prop := check_header_stmt_for true.    (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition open_result_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (L : alayout) (RNG : footprint) (FL : list fblock) (CL : list cblk) (lo EB : Z) (m : mem) (o : option hptr)
      (keepFB : list cblk -> Prop)   (* [comment removed for export] *)
      (okFB : list cblk -> pcapT -> Prop)
      : ((list Z) + pcapT) -> PS -> footprint -> machine_state -> Prop :=
    fun r s' RNG' ms' => fp_le RNG RNG' /\ exists a0v m' FB', hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v m' ms'
      /\ ps_outfile s' = o /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ ~ (EB <= a < EB + 256)) m m'
      /\ match r with
         | inl msg => exists junk', a0v = Z_to_bv 64 0 /\ keepFB FB' /\ GIO L RNG' s' CL FB' FL m'
             /\ rw_cells asegs m' EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk'] /\ Z.of_nat (length msg) < 256
             /\ Forall (fun z => 0 < z < 256) msg
         | inr p => exists P PB, a0v = Z_to_bv 64 P /\ okFB FB' p /\ GIO L RNG' s' (CL ++ PB) FB' FL m' /\ PCR P p PB FB' m'
             /\ (exists e, rw_cells asegs m' EB [CB 256 e])
         end.

  Definition fopen_offline_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (trC : list Z) (lo FA EB : Z) (f : hptr) (ej : list byte) (fuel : nat),
      SPOA L RNG sp tp s CL FB FL lo PCAP_L3_STACK m ->
      ucallerA (depth_fopen_offline) L m sp s0 ra trC -> traces_fopen_offline TP L (bv_unsigned ra) trC -> nofr (frames_fopen_offline) FL -> In (f, FA, FILE_BLOCK) FB ->
      a0 = Z_to_bv 64 FA -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 EB ->
      rw_cells asegs m EB [CB 256 ej] -> cobjA RNG m FL CL EB 256 -> EB mod 8 = 0 ->
      implMG RNG (Pcap.pcap_fopen_offline_with_tstamp_precision MOps PR fuel f 0) s
        (open_result_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL lo EB m (ps_outfile s)
           (fun FB' => FB' = FB) (fun FB' p => FB' = FB /\ pc_rfile p = f))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PCAP_FOPEN_OFFLINE_WTP_ENTRY) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition open_offline_stmt_at (ENTRY : Z) (a_err : word -> word -> word) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (L : alayout) (RNG : footprint) (s : PS) (CL FB : list cblk) (FL : list fblock) (trC : list Z) (lo NAME EB : Z) (name slack ej : list byte) (fuel : nat),
      SPOA L RNG sp tp s CL FB FL lo PCAP_L4_STACK m ->
      ucallerA (depth_open_offline ENTRY) L m sp s0 ra trC -> traces_open_offline TP ENTRY L (bv_unsigned ra) trC -> nofr (frames_open_offline ENTRY) FL ->
      a0 = Z_to_bv 64 NAME -> a_err a1 a2 = Z_to_bv 64 EB -> (ENTRY = PCAP_OPEN_OFFLINE_WTP_ENTRY -> a1 = Z_to_bv 64 0) ->
      bytes_at asegs m NAME (name ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) name -> (1 <= length name <= 4095)%nat ->
      nth_error name 0 <> Some (Z_to_bv 8 45) ->
      open_name_ok false name ->   (* [comment removed for export] *)
      (- (NAME + Z.of_nat (length name) + 1)) mod 8 <= Z.of_nat (length slack) ->
      cobjA RNG m FL CL NAME (Z.of_nat (length name) + 1) -> clocA FL CL NAME (Z.of_nat (length name) + 1 + Z.of_nat (length slack)) -> rng RNG NAME (Z.of_nat (length name) + 1 + Z.of_nat (length slack)) ->   (* [comment removed for export] *)
      rw_cells asegs m EB [CB 256 ej] -> cobjA RNG m FL CL EB 256 -> EB mod 8 = 0 ->
      (NAME + Z.of_nat (length name) + 1 + Z.of_nat (length slack) <= EB \/ EB + 256 <= NAME) ->
      implMG RNG (Pcap.pcap_open_offline MOps PR fuel (map bv_unsigned name)) s
        (open_result_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CL lo EB m (ps_outfile s)
           (fun FB' => FB' = FB) (fun FB' p => exists FA, FB' = (pc_rfile p, FA, FILE_BLOCK) :: FB))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ENTRY) fc None m (seg_rom asegs)).
  Definition pcap_open_offline_stmt : Prop := open_offline_stmt_at PCAP_OPEN_OFFLINE_ENTRY (fun a1 _ => a1).
  Definition pcap_open_offline_wtp_stmt : Prop := open_offline_stmt_at PCAP_OPEN_OFFLINE_WTP_ENTRY (fun _ a2 => a2).

  (* [comment removed for export] *)
End Ifaces.
End TwB.
