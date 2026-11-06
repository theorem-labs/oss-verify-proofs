(** * reac-pw/fuzz_link (plain): the driver's exit after a library call, with link's memory FILE open.

    From its first mark on, link's library leaves the open-file list holding the memory FILE (MemFile.v); so
    at exit [__stdio_exit] (plain 0x199a4) walks that FILE before it closes stdin / stdout / stderr. The
    released exit walks the frame relocated from pcap (YN35.v [src0_exit], YN34.v [diag_exit_check]) read
    [ofl_head] from the image (it was 0). Here [ofl_head] is a byte of the slot's [G], so after a library call
    the driver's symbolic memory no longer knows it; [stdio_exit_two_arm] reads it from the GI conjunct
    [mf_gi] instead and splits:
    - head 0: [ld s0,0(a0)] at 0x199b4 loads 0, [bnez s0] falls through to 0x199bc: the released walk;
    - head f: the loop body 0x19ae4-0x19b34 runs close_file on the FILE at [f]. [memfile_at] fixes what it reads
      ([memfile_close_reads]: [lock] = -1, so no __lockfile; [write] = mwrite; [rpos] = [rend] = 0, so no
      seek; [next] = 0, so the loop ends at 0x199bc). When the window is empty or holds no byte
      ([wpos] = [wbase]) nothing is called; when it holds bytes, [f->write (f, 0, 0)] = mwrite runs, and the
      arm uses the mwrite contract [mwrite_exit_contract] below, a PREMISE: mwrite's walk is the printf
      lane's (link/briefs/W2-printf.md, deliverable 4), not on this branch yet.
    Every arm ends at 0x199bc in ONE symbolic state [ss2] (the caller-saved registers fresh, [s0] = 0, the
    stack below [sp] cut for mwrite's frame), so each exit site checks the rest of the exit once, from [ss2]:
    [exit_mf_check] / [diag_mf_check] are YN35 / YN34's checks run from [ss2].

    The released close_file proof the proof index names (libpcap/fuzz_pcap/lib/E2/Spec/StdioCore.v [close_file],
    a definition of the E2 functional model: write the buffer when it holds bytes, then sync the read
    position) is a model, not a machine walk of this frame; the arm above walks the same two branches on link's
    image with this frame's symbolic executor, new. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0k YK0n YK0p YP0n YM06 YM02.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0x YO0d YO0e YO05 YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YH00 YH01 YH03 YH02 YN35 YN34.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN03 YL07 YL01 YL00 YL0d YL0g YL05 YL0s YL0k GIWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YI06 YI16 YI14 YI5b YI5c YL0i YL06.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YN2j YN3u.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import MemFileSink MemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import SlotAgree AllocSlots MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YP03_cfw YL0d_cfw YN34b_cfw YN35_cfw.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(** ** Addresses, read from link's plain image ([__stdio_exit], plain 0x199a4-0x19b44; MemFile.v [link_mf_code]
    checks the loop's instructions) *)
Definition OFLH : Z := 0x95cc8.        (* ofl_head (.symtab); __ofl_lock +0xc / +0x10 / +0x1c *)
Definition SX_HEAD_LD : Z := 0x199b4.  (* +0x10 ld s0,0(a0): a0 = &ofl_head *)
Definition SX_CONT : Z := 0x199bc.     (* +0x18: after the list loop (bnez s0 at +0x14, beqz s0 at 0x19ae0) *)
Definition SX_MW_RA : Z := 0x19b14.    (* return address of the loop's jalr a3 at 0x19b10 (f->write) *)
Definition MW_STACK : Z := 256.        (* mwrite's frame: 48 bytes, at most two deep, and leaf memcpy *)
Definition MW_G : list (Z * Z) := [(mf_buf link_mf, mf_size link_mf)].  (* g_said: mwrite's memcpy target *)

Lemma OFLH_head : @sk_ofl_head src0_sink_head = OFLH.
Proof. reflexivity. Qed.

(** ** The mwrite contract, a premise of the head-f arm

    [mw_pre] is what the loop gives mwrite at 0x19b10 ([a0] = the FILE, [a1] = [a2] = 0, [ra] = 0x19b14);
    [mw_post] is what the arm needs back: the callee-saved registers, [a0] = 0 (mwrite returns its [len], 0),
    the FILE still a memory FILE ([memfile_at]: the loop then reads [rpos], [rend], [next] from it), the
    allocator unchanged, and only the FILE's block, [g_said] (mwrite's memcpy), errno (ENOSPC) and its own
    stack frame written. The printf lane's mwrite walk discharges it. *)
Section mw.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition mw_pre (ra : Z) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (f : Z) : Prop :=
  MR L A mem md /\ WF A /\ bounded A /\
  getr regs 1 = Z_to_bv 64 ra /\
  spZ regs mod 16 = 0 /\ alloc_ceiling + MW_STACK <= spZ regs /\ spZ regs < 2 ^ 63 /\
  (forall a, spZ regs - MW_STACK <= a < spZ regs -> writable_at segs mem a) /\
  getr regs 4 = Z_to_bv 64 (ms_tp B) /\
  (forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at segs mem a) /\
  getr regs 10 = Z_to_bv 64 f /\ getr regs 11 = Z_to_bv 64 0 /\ getr regs 12 = Z_to_bv 64 0 /\
  In (f, MF_BLOCK) (blocks L A) /\ memfile_at B link_mf mem f /\
  (forall a, in_globals MW_G a -> writable_at segs mem a) /\
  rodata_ok B mem.

Definition mw_post (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (f : Z) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  MR L A mem' md /\
  getr regs' 10 = Z_to_bv 64 0 /\
  regs_preserved regs regs' /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ lib_scratch B MW_STACK regs a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
     ~ (errno_addr B <= a < errno_addr B + 4) -> ~ in_globals MW_G a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall q k i, In (q, k) (user_blocks A) -> ptr_addr L q <> f -> 0 <= i < k ->
     mbyte segs mem' (ptr_addr L q + i) = mbyte segs mem (ptr_addr L q + i)) /\
  (forall a, lib_scratch B MW_STACK regs a -> writable_at segs mem' a) /\
  memfile_at B link_mf mem' f.

Definition mwrite_exit_contract (ra : Z) : Prop :=
  forall L A regs mem md f, mw_pre ra L A regs mem md f ->
  SR segs (mkCfg (mkst regs (Z_to_bv 64 (mf_write link_mf)) mem (seg_rom segs)) md)
    (fun c' => exists regs' mem', c' = mkCfg (mkst regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md /\
       mw_post L A regs mem md f regs' mem').

(** The same contract in the cut-free world (SlotAgree.v [SRcf]), for the [_cfw] driver files. *)
Definition mwrite_exit_contract_cf (ra : Z) : Prop :=
  forall L A regs mem md f, mw_pre ra L A regs mem md f ->
  SRcf B (mkCfg (mkst regs (Z_to_bv 64 (mf_write link_mf)) mem (seg_rom segs)) md)
    (fun c' => exists regs' mem', c' = mkCfg (mkst regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md /\
       mw_post L A regs mem md f regs' mem').

(** The frame facts [mem_ok_call_frame] needs, from [mw_post] (as YL06.v [lib_post_frame_T] from a library
    post). *)
Lemma mw_post_frame :
  forall L A regs mem md f regs' mem' (E : env) sp_off keep (blks : list (nat * Z)),
  mw_post L A regs mem md f regs' mem' ->
  keep_check B keep = true -> keep_avoid MW_G keep = true ->
  errno_addr B + 4 <= alloc_ceiling ->
  bv_unsigned (getr regs 2) = bv_unsigned (ew E 0) + sp_off ->
  alloc_ceiling + MW_STACK <= bv_unsigned (getr regs 2) ->
  (forall n sz, In (n, sz) blks -> exists q, In (q, sz) (user_blocks A) /\ ptr_addr L q = bv_unsigned (ew E n) /\
     ptr_addr L q <> f) ->
  (forall a, alloc_ceiling <= a -> a < 2 ^ 64 ->
     ~ (bv_unsigned (ew E 0) + sp_off - MW_STACK <= a < bv_unsigned (ew E 0) + sp_off) ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a -> writable_at segs mem' a)) /\
  (forall a, bv_unsigned (ew E 0) + sp_off - MW_STACK <= a < bv_unsigned (ew E 0) + sp_off -> writable_at segs mem' a) /\
  (forall a, in_ivl keep a = true ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a -> writable_at segs mem' a)) /\
  (forall a, in_ivl [(errno_addr B, errno_addr B + 4)] a = true -> writable_at segs mem' a) /\
  (forall n sz i, In (n, sz) blks -> 0 <= i < sz ->
     mbyte segs mem' (bv_unsigned (ew E n) + i) = mbyte segs mem (bv_unsigned (ew E n) + i) /\
     writable_at segs mem' (bv_unsigned (ew E n) + i)).
Proof using.
  intros L A regs mem md f regs' mem' E sp_off keep blks HP Hkc Hka Herr Hsp Hsplo Hblks.
  destruct HP as (HMR' & Ha0 & Hregs & Hfr & Hfri & Hbk & Hscr & _).
  split; [| split; [| split; [| split]]].
  - intros a Ha Ha64 Hns. destruct (Hfr a) as [H1 H2].
    + exact (conj Ha Ha64).
    + unfold lib_scratch, spZ. rewrite Hsp. intros [Hs|Hs]; lia.
    + split; [exact H1 | intros W; apply H2; exact W].
  - intros a Ha. apply Hscr. unfold lib_scratch, spZ. rewrite Hsp. left. exact Ha.
  - intros a Ha. destruct (keep_check_sound B keep a Hkc Ha) as (Himg & Hlow & Hst & Hctx & Herrno).
    destruct (Hfri a Himg Hst Hctx Herrno (keep_avoid_sound MW_G keep a Hka Ha)) as [H1 H2].
    split; [exact H1 | intros W; apply H2; exact W].
  - intros a Ha. destruct (in_ivl_In _ a Ha) as (q & Hq & Haq). destruct Hq as [<-|[]]. cbn [fst snd] in Haq.
    apply Hscr. unfold lib_scratch. right. exact Haq.
  - intros n sz i Hin Hi. destruct (Hblks n sz Hin) as (q & HinA & Hq & Hqf). rewrite <- Hq. split.
    + exact (Hbk q sz i HinA Hqf Hi).
    + apply YL01.present_writable.
      exact (proj1 (mr_blocks B MR (aa_laws API) L A mem' md q sz i HMR' HinA Hi)).
Qed.

(** The symbolic state at mwrite's return, from the state at the call (as YL06.v [st_ok_after_lib_T]). *)
Theorem st_ok_after_mw :
  forall k E ss regs pc mem md L A f regs' mem' (sp_off : Z) keep (blks : list (nat * Z))
    (l1 : list (nat * YP09.region)),
  st_ok segs E ss (mkst regs pc mem (seg_rom segs)) -> stack_anchored E (ss_facts ss) ->
  ss_atoms_lt k ss = true ->
  mw_post L A regs mem md f regs' mem' ->
  keep_check B keep = true -> keep_avoid MW_G keep = true -> errno_addr B + 4 <= alloc_ceiling ->
  bv_unsigned (getr regs 2) = bv_unsigned (ew E 0) + sp_off ->
  alloc_ceiling + MW_STACK <= bv_unsigned (getr regs 2) ->
  (forall n sz, In (n, sz) blks -> exists q, In (q, sz) (user_blocks A) /\ ptr_addr L q = bv_unsigned (ew E n) /\
     ptr_addr L q <> f) ->
  relayout_ok segs (ss_mem ss) l1 = true ->
  mem_atoms_lt k (map snd l1) = true ->
  call_frame_check (ss_facts ss) sp_off MW_STACK keep [(errno_addr B, errno_addr B + 4)] blks (map snd l1) = true ->
  st_ok segs (havoc E k (map (getr regs') caller_saved))
    (mkSS SX_MW_RA (sr_set (sr_sets (ss_regs ss) (junk_upd k caller_saved)) 10%bv (SLit 0)) (map snd l1) None (ss_facts ss))
    (mkst regs' (Z_to_bv 64 SX_MW_RA) mem' (seg_rom segs)).
Proof using.
  intros k E ss regs pc mem md L A f regs' mem' sp_off keep blks l1
    HS HSA Hat HP Hkc Hka Herr Hsp Hsplo Hblks Hrl Hma Hcf.
  assert (HS1 : st_ok segs (havoc E k (map (getr regs') caller_saved))
    (mkSS SX_MW_RA (sr_sets (ss_regs ss) (junk_upd k caller_saved)) (map snd l1) None (ss_facts ss))
    (mkst regs' (Z_to_bv 64 SX_MW_RA) mem' (seg_rom segs))).
  { change (junk_upd k caller_saved) with ([] ++ junk_upd k caller_saved).
    eapply (st_ok_splice_havoc segs k E ss regs regs' pc SX_MW_RA mem mem' (map snd l1) [] caller_saved HS Hat).
    - vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - reflexivity.
    - exact Hma.
    - cbn [map fst app]. apply regs_preserved_frame. destruct HP as (_ & _ & Hregs & _). exact Hregs.
    - constructor.
    - destruct HS as (_ & _ & _ & _ & _ & _ & _ & HM & HG). cbn [ms_mem mkst] in HM.
      destruct (mw_post_frame L A regs mem md f regs' mem' E sp_off keep blks
        HP Hkc Hka Herr Hsp Hsplo Hblks) as (F1 & F2 & F3 & F5 & F4).
      apply (mem_ok_call_frame segs (ss_facts ss) sp_off MW_STACK keep [(errno_addr B, errno_addr B + 4)] blks E mem mem'
        F1 F2 F3 F5 F4 HG HSA).
      + eapply mem_ok_relayout; [exact HM | exact Hrl].
      + exact Hcf. }
  apply (st_ok_regs segs _ _ _ _ HS1).
  cbn [ss_regs]. intros r. destruct (decide (r = 10%bv)) as [->|Hne].
  - rewrite sr_get_set_same by reflexivity.
    destruct HS1 as (_ & _ & _ & _ & _ & _ & Hregs1 & _). rewrite <- (Hregs1 10%bv). cbn [ms_regs mkst].
    destruct HP as (_ & Ha0 & _). rewrite Ha0. reflexivity.
  - rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.

(** What the symbolic state at the call gives [mw_pre] (as YL05.v [lib_pre_intro]). *)
Definition mw_pre_check (ss : sstate) (sp_off : Z) (kf : nat) : bool :=
  sv_eqb (sr_get (ss_regs ss) 2) (SOff 0 sp_off) &&
  sv_eqb (sr_get (ss_regs ss) 4) (SLit (ms_tp B)) &&
  sv_eqb (sr_get (ss_regs ss) 1) (SLit SX_MW_RA) &&
  sv_eqb (sr_get (ss_regs ss) 10) (SOff kf 0) &&
  sv_eqb (sr_get (ss_regs ss) 11) (SLit 0) && sv_eqb (sr_get (ss_regs ss) 12) (SLit 0) &&
  (sp_off mod 16 =? 0) &&
  match fact_of (f_atoms (ss_facts ss)) 0 with
  | Some f =>
      (CEIL_MIN <=? af_lo f) && (CEIL_MIN + MW_STACK <=? af_lo f + sp_off) && (af_hi f + sp_off <? 2 ^ 63) &&
      (4 <=? af_al2 f)
  | None => false
  end &&
  existsb (fun r => obase_eqb (r_base r) (Some 0%nat) && (r_wlo r <=? sp_off - MW_STACK) && (sp_off <=? r_whi r)) (ss_mem ss) &&
  existsb (fun r => obase_eqb (r_base r) None && (r_wlo r <=? errno_addr B) && (errno_addr B + 4 <=? r_whi r)) (ss_mem ss).

Lemma mw_pre_intro : forall E ss ms sp_off kf f,
  st_ok segs E ss ms -> stack_anchored E (ss_facts ss) ->
  mw_pre_check ss sp_off kf = true -> ew E kf = Z_to_bv 64 f -> 0 <= f < 2 ^ 64 ->
  getr (ms_regs ms) 1 = Z_to_bv 64 SX_MW_RA /\
  spZ (ms_regs ms) mod 16 = 0 /\ alloc_ceiling + MW_STACK <= spZ (ms_regs ms) /\ spZ (ms_regs ms) < 2 ^ 63 /\
  (forall a, spZ (ms_regs ms) - MW_STACK <= a < spZ (ms_regs ms) -> writable_at segs (ms_mem ms) a) /\
  getr (ms_regs ms) 4 = Z_to_bv 64 (ms_tp B) /\
  (forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at segs (ms_mem ms) a) /\
  getr (ms_regs ms) 10 = Z_to_bv 64 f /\ getr (ms_regs ms) 11 = Z_to_bv 64 0 /\ getr (ms_regs ms) 12 = Z_to_bv 64 0 /\
  bv_unsigned (getr (ms_regs ms) 2) = bv_unsigned (ew E 0) + sp_off.
Proof.
  intros E ss ms sp_off kf f HS HSA Hck Hkf Hf.
  unfold mw_pre_check in Hck.
  apply andb_prop in Hck as [Hck Herr]. apply andb_prop in Hck as [Hck Hstk]. apply andb_prop in Hck as [Hck Hf0].
  apply andb_prop in Hck as [Hck Hmod]. apply andb_prop in Hck as [Hck Ha2]. apply andb_prop in Hck as [Hck Ha1].
  apply andb_prop in Hck as [Hck Ha0]. apply andb_prop in Hck as [Hck Hra]. apply andb_prop in Hck as [Hsp Htp].
  apply sv_eqb_eq in Hsp. apply sv_eqb_eq in Htp. apply sv_eqb_eq in Hra. apply sv_eqb_eq in Ha0.
  apply sv_eqb_eq in Ha1. apply sv_eqb_eq in Ha2. apply Z.eqb_eq in Hmod.
  destruct HS as (_ & _ & _ & _ & _ & _ & Hregs & HM & HG).
  destruct (fact_of (f_atoms (ss_facts ss)) 0) as [fa|] eqn:Hfa; [|discriminate].
  pose proof (fact_of_sound E _ 0%nat fa (proj1 HG) Hfa) as (Hlohi & Hal & Hal2).
  apply andb_prop in Hf0 as [Hf0 Z]. apply andb_prop in Hf0 as [Hf0 Z0]. apply andb_prop in Hf0 as [Hf0 Z1].
  apply Z.leb_le in Hf0. apply Z.leb_le in Z1. apply Z.ltb_lt in Z0. apply Z.leb_le in Z.
  pose proof (stack_anchored_sound E (ss_facts ss) 0 (af_lo fa - CEIL_MIN) HSA
    ltac:(unfold anch_lo; rewrite (fact_lo_of _ _ _ Hfa), (proj2 (Z.leb_le _ _) Hf0); reflexivity)) as Hanc.
  pose proof (mod16_of_al2 _ _ Z Hal) as H16.
  assert (Hac : 0 <= alloc_ceiling) by (pose proof YM05.alloc_ceiling_val; lia).
  assert (Hcm : 0 <= CEIL_MIN) by (apply Z.leb_le; vm_compute; reflexivity).
  assert (HMW : MW_STACK = 256) by reflexivity.
  assert (Hsp2 : bv_unsigned (getr (ms_regs ms) 2) = bv_unsigned (ew E 0) + sp_off).
  { rewrite (Hregs 2%bv), Hsp. cbn [sv_denot]. rewrite Z_to_bv_unsigned.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
  unfold spZ. rewrite Hsp2.
  split; [rewrite (Hregs 1%bv), Hra; reflexivity|].
  split; [rewrite Z.add_mod, H16, Hmod by lia; reflexivity|].
  split; [lia|]. split; [lia|]. split.
  { apply existsb_In in Hstk as (r & Hr & Hc). apply andb_prop in Hc as [Hc Hw2]. apply andb_prop in Hc as [Hb Hw1].
    apply obase_eqb_eq in Hb. apply Z.leb_le in Hw1. apply Z.leb_le in Hw2.
    intros a Ha. destruct (mem_ok_region segs E _ _ r HM Hr) as (_ & _ & Hw & _). rewrite Hb in Hw. cbn [base_val] in Hw.
    replace a with (bv_unsigned (ew E 0%nat) + (a - bv_unsigned (ew E 0%nat))) by lia. apply Hw. lia. }
  split; [rewrite (Hregs 4%bv), Htp; reflexivity|].
  split.
  { apply existsb_In in Herr as (r & Hr & Hc). apply andb_prop in Hc as [Hc Hw2]. apply andb_prop in Hc as [Hb Hw1].
    apply obase_eqb_eq in Hb. apply Z.leb_le in Hw1. apply Z.leb_le in Hw2.
    intros a Ha. destruct (mem_ok_region segs E _ _ r HM Hr) as (_ & _ & Hw & _). rewrite Hb in Hw. cbn [base_val] in Hw.
    replace a with (0 + a) by lia. apply Hw. lia. }
  split.
  { rewrite (Hregs 10%bv), Ha0. cbn [sv_denot]. rewrite Hkf, Z.add_0_r, lit64_small by exact Hf. reflexivity. }
  split; [rewrite (Hregs 11%bv), Ha1; reflexivity|].
  split; [rewrite (Hregs 12%bv), Ha2; reflexivity|].
  reflexivity.
Qed.
End mw.

Definition mwrite_exit_contract_all {rc : YM05.RunCeil} (B : malloc_syms) (API : AllocAPI B) : Prop :=
  forall fx : YK11.FPState, @mwrite_exit_contract fx rc B API SX_MW_RA.

(** ** Checks on symbolic states (all decided by vm_compute at the exit site) *)

(** Regions kept while the FILE block is in the symbolic memory: the absolute ones and those based at an
    atom anchored above the allocation ceiling (the stack). A region based at another atom is a driver block,
    which the FILE block is not; the exit never reads one. *)
Definition sx_keep_region (F : facts) (r : YP09.region) : bool :=
  match r_base r with None => true | Some n => match anch_lo F n with Some _ => true | None => false end end.
Definition sx_dropl (F : facts) (l : list (nat * YP09.region)) : list (nat * YP09.region) :=
  filter (fun p => sx_keep_region F (snd p)) l.

(** Where a region may lie beside the FILE block: an absolute region inside ONE image segment (the block is
    outside the image, AllocExtra [ax_blocks_img], and is one interval, so it misses the whole segment), or a
    region based at an anchored atom, at or above the allocation ceiling (the block is below it). *)
Definition seg_one (lo hi : Z) : bool :=
  existsb (fun s => (bv_unsigned (fst s) <=? lo) && (hi <=? bv_unsigned (fst s) + bv_unsigned (snd s)) &&
    (0 <? bv_unsigned (snd s))) (segments_reserved src0segs).
Definition rfx_region_ok (F : facts) (r : YP09.region) : bool :=
  match r_base r with
  | None => (r_lo r <=? r_hi r) && seg_one (r_lo r) (r_hi r)
  | Some n => match anch_lo F n with Some K => 0 <=? K + r_lo r | None => false end
  end.
Definition rfx_ok (F : facts) (rs : smem) : bool := forallb (rfx_region_ok F) rs.

(** The FILE block as a region based at atom [kf] (no write window: the arm only reads it). *)
Definition rf_ch8 (off : Z) (v : sv) : chunk := mkChunk off (CVal 8 v).
Definition rf_pre_chunks (wpos wbase : sv) : list chunk :=
  [mkChunk 140 (CVal 4 (SLit U32M1)); rf_ch8 72 (SLit (mf_write link_mf)); rf_ch8 8 (SLit 0); rf_ch8 16 (SLit 0);
   rf_ch8 112 (SLit 0); rf_ch8 40 wpos; rf_ch8 56 wbase].
Definition rf_post_chunks : list chunk := [rf_ch8 8 (SLit 0); rf_ch8 16 (SLit 0); rf_ch8 112 (SLit 0)].
Definition rf_region (kf : nat) (cs : list chunk) : YP09.region := YP09.mkRegion (Some kf) 0 MF_ZEROED 0 0 cs.

Definition sx_addc (ss : sstate) (c : chunk) : option sstate :=
  match YN3u.add_chunk_sem (ss_mem ss) None c with
  | Some (rs', _) => Some (mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) rs' (ss_resv ss) (ss_facts ss))
  | None => None
  end.
Definition sx_addr (r : YP09.region) (ss : sstate) : sstate :=
  mkSS (ss_pc ss) (ss_regs ss) (r :: ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition sx_fatom : afact := mkAF 4096 CEIL_MAX 4.

Definition sx_base (s1 : sstate) : sstate :=
  mkSS (ss_pc s1) (ss_regs s1) (map snd (sx_dropl (ss_facts s1) (same_layout (ss_mem s1)))) (ss_resv s1) (ss_facts s1).

(** A relayout onto a given target list: each target region with the first region it derives from. *)
Fixpoint first_parent (rs : smem) (r : YP09.region) (i : nat) : nat :=
  match rs with [] => i | p :: rs' => if derived_ok src0segs p r then i else first_parent rs' r (S i) end.
Definition realign (rs M : smem) : list (nat * YP09.region) := map (fun r => (first_parent rs r 0, r)) M.
Lemma realign_snd : forall rs M, map snd (realign rs M) = M.
Proof. intros rs M. unfold realign. rewrite map_map. cbn. apply map_id. Qed.

Fixpoint svl_eqb (l1 l2 : list sv) : bool :=
  match l1, l2 with
  | [], [] => true
  | a :: l1', b :: l2' => sv_eqb a b && svl_eqb l1' l2'
  | _, _ => false
  end.
Lemma svl_eqb_eq : forall l1 l2, svl_eqb l1 l2 = true -> l1 = l2.
Proof.
  induction l1 as [|a l1 IH]; intros [|b l2] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply sv_eqb_eq in H1. subst. f_equal. apply IH. exact H2.
Qed.
Fixpoint anch_eqb (l1 l2 : list (nat * Z)) : bool :=
  match l1, l2 with
  | [], [] => true
  | a :: l1', b :: l2' => Nat.eqb (fst a) (fst b) && Z.eqb (snd a) (snd b) && anch_eqb l1' l2'
  | _, _ => false
  end.
Lemma anch_eqb_eq : forall l1 l2, anch_eqb l1 l2 = true -> l1 = l2.
Proof.
  induction l1 as [|[a x] l1 IH]; intros [|[b y] l2] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H H2]. apply andb_prop in H as [H0 H1]. apply Nat.eqb_eq in H0. apply Z.eqb_eq in H1.
  subst. f_equal. apply IH. exact H2.
Qed.

Definition SX_KF : nat := 512.           (* the FILE's atom; every atom of an exit state lies below it *)
Definition SX_KW : nat := 513.           (* the window's [wpos] when it holds bytes *)
Definition SX_K3 : nat := 514.           (* mwrite's fresh caller-saved registers, 514-529 *)
Definition SX_K : nat := 530.            (* the fresh caller-saved registers of [ss2], 530-545 *)
Definition SX_KD : nat := 600.           (* the writev of a diagnostic exit, after [ss2] *)

Definition sx_upd : list (reg * sv) := (8%bv, SLit 0) :: junk_upd SX_K caller_saved.

(** The one state every arm reaches at 0x199bc. *)
Definition sx_ss2 (sp_off : Z) (s1 : sstate) : sstate :=
  mkSS SX_CONT (sr_sets (ss_regs s1) sx_upd)
    (map snd (sx_dropl (ss_facts s1) (precall src0_keepG sp_off MW_STACK (ss_mem s1)))) None (ss_facts s1).

(** An arm's end state [se] gives [ss2]: at 0x199bc, [s0] = 0, the registers outside [sx_upd] as at 0x199b4,
    its memory relayouts onto [ss2]'s. *)
Definition sx_end_ok (sp_off : Z) (s1 se : sstate) : bool :=
  (ss_pc se =? SX_CONT) && match ss_resv se with None => true | Some _ => false end &&
  sv_eqb (sr_get (ss_regs se) 8) (SLit 0) &&
  svl_eqb (sr_sets (ss_regs se) sx_upd) (sr_sets (ss_regs s1) sx_upd) &&
  ss_atoms_lt SX_K se &&
  relayout_ok src0segs (ss_mem se) (realign (ss_mem se) (ss_mem (sx_ss2 sp_off s1))).

Definition sx_sp_off (s1 : sstate) : Z :=
  match sr_get (ss_regs s1) 2 with SOff 0 o => o | _ => 0 end.

(** The arms' start states. *)
Definition sx_arm0 (s1 : sstate) : option sstate := sx_addc (sx_base s1) (rf_ch8 OFLH (SLit 0)).
Definition sx_armf (s1 : sstate) (wpos wbase : sv) : option sstate :=
  sx_addc (sx_addr (rf_region SX_KF (rf_pre_chunks wpos wbase)) (add_atom (sx_base s1) SX_KF sx_fatom))
    (rf_ch8 OFLH (SOff SX_KF 0)).
Definition sx_condk : acond := mkAC BC_NE (SOff SX_KW 0) (SOff SX_KF 280).
Definition sx_armk (s1 : sstate) : option sstate :=
  sx_addc (sx_addr (rf_region SX_KF (rf_pre_chunks (SOff SX_KW 0) (SOff SX_KF 280)))
             (add_cond (add_atom (sx_base s1) SX_KF sx_fatom) sx_condk))
    (rf_ch8 OFLH (SOff SX_KF 0)).

(** The mwrite call: the relayout at the call and the state at the return, with the FILE region read again. *)
Definition sx_l1 (sp_off : Z) (sc : sstate) : list (nat * YP09.region) :=
  gcarve [(OFLH, 8)] (drop_base SX_KF (precall src0_keepG sp_off MW_STACK (ss_mem sc))).
Definition sx_ret (sp_off : Z) (sc : sstate) : sstate :=
  sx_addr (rf_region SX_KF rf_post_chunks)
    (mkSS SX_MW_RA (sr_set (sr_sets (ss_regs sc) (junk_upd SX_K3 caller_saved)) 10%bv (SLit 0))
       (map snd (sx_l1 sp_off sc)) None (ss_facts sc)).

Definition sx_call_ok (sp_off : Z) (ss sf sc : sstate) : bool :=
  (ss_pc sc =? mf_write link_mf) && match ss_resv sc with None => true | Some _ => false end &&
  mw_pre_check src0_msyms sc sp_off SX_KF &&
  wr_check src0_msyms (ss_facts sf) src0_keep (ss_mem sf) &&
  anch_eqb (anchored_atoms (ss_facts sf)) (anchored_atoms (ss_facts ss)) &&
  anch_eqb (anchored_atoms (ss_facts sc)) (anchored_atoms (ss_facts ss)) &&
  keep_check src0_msyms src0_keepG && keep_avoid MW_G src0_keepG && (errno_addr src0_msyms + 4 <=? CEIL_MIN) &&
  relayout_ok src0segs (ss_mem sc) (sx_l1 sp_off sc) &&
  ss_atoms_lt SX_K3 sc && mem_atoms_lt SX_K3 (map snd (sx_l1 sp_off sc)) &&
  call_frame_check (ss_facts sc) sp_off MW_STACK src0_keepG [(errno_addr src0_msyms, errno_addr src0_msyms + 4)] []
    (map snd (sx_l1 sp_off sc)) &&
  rfx_ok (ss_facts sc) (map snd (sx_l1 sp_off sc)) &&
  ro_check src0_msyms (ss_mem sc).

(** An arm that calls nothing: its start state's write windows are framed (so the allocator's MR survives
    the run, [MR_after_frame]), its anchored atoms are the exit's, and its end state gives [ss2]. *)
Definition sx_arm_ok (sp_off : Z) (ss s1 : sstate) (o : option sstate) : bool :=
  match o with
  | Some s =>
      wr_check src0_msyms (ss_facts s) src0_keep (ss_mem s) &&
      anch_eqb (anchored_atoms (ss_facts s)) (anchored_atoms (ss_facts ss)) &&
      match run_to_check src0segs src0tbl SX_CONT s with Some se => sx_end_ok sp_off s1 se | None => false end
  | None => false
  end.

Definition sx_armk_ok (sp_off : Z) (ss s1 : sstate) : bool :=
  match sx_armk s1 with
  | Some sf =>
      match run_to_check src0segs src0tbl (mf_write link_mf) sf with
      | Some sc => sx_call_ok sp_off ss sf sc &&
          wr_check src0_msyms (ss_facts (sx_ret sp_off sc)) src0_keep (ss_mem (sx_ret sp_off sc)) &&
          match run_to_check src0segs src0tbl SX_CONT (sx_ret sp_off sc) with
          | Some se => sx_end_ok sp_off s1 se
          | None => false
          end
      | None => false
      end
  | None => false
  end.

(** Everything the split needs, on the exit-check start state [ss] and the state [s1] at 0x199b4. *)
Definition sx_split (ss : sstate) : option sstate :=
  match run_to_check src0segs src0tbl SX_HEAD_LD ss with
  | None => None
  | Some s1 =>
      let sp_off := sx_sp_off s1 in
      if g_wr_check src0_G (ss_facts ss) (ss_mem ss) && wr_check src0_msyms (ss_facts ss) src0_keep (ss_mem ss) &&
         match ss_resv s1 with None => true | Some _ => false end &&
         sv_eqb (sr_get (ss_regs s1) 10) (SLit OFLH) &&
         ss_atoms_lt SX_KF s1 && ss_atoms_lt SX_KF (sx_base s1) &&
         anch_eqb (anchored_atoms (ss_facts s1)) (anchored_atoms (ss_facts ss)) &&
         forallb (fun a => Nat.ltb (fst a) SX_KF) (anchored_atoms (ss_facts ss)) &&
         mem_atoms_lt SX_KF (ss_mem (sx_ss2 sp_off s1)) &&
         rfx_ok (ss_facts s1) (ss_mem (sx_base s1)) &&
         relayout_ok src0segs (ss_mem s1) (sx_dropl (ss_facts s1) (same_layout (ss_mem s1))) &&
         sx_arm_ok sp_off ss s1 (sx_arm0 s1) &&
         sx_arm_ok sp_off ss s1 (sx_armf s1 (SLit 0) (SLit 0)) &&
         sx_arm_ok sp_off ss s1 (sx_armf s1 (SOff SX_KF 280) (SOff SX_KF 280)) &&
         sx_armk_ok sp_off ss s1
      then Some (sx_ss2 sp_off s1) else None
  end.

(** The rest of the exit runs from [ss2] with the three static chunks (the GOT slot of the stack guard,
    [__libc + 3], the guard) added back, as every driver call site does ([drv_add_statics]): [sx_ss2] cut
    them for the mwrite call ([precall]), and close_file(stdout)'s write path loads the guard through the
    GOT. [SX_KG] is the guard's fresh atom, above [ss2]'s atoms and below [SX_KD]. *)
Definition SX_KG : nat := 546.
Definition sx_statics (ss2 : sstate) : option sstate :=
  match drv_add_statics src0_msyms (ss_mem ss2) SX_KG with
  | Some rs => Some (mkSS (ss_pc ss2) (ss_regs ss2) rs (ss_resv ss2) (ss_facts ss2))
  | None => None
  end.

Definition exit_mf_check (ss : sstate) (code : Z) : bool :=
  match sx_split ss with
  | Some ss2 =>
      ss_atoms_lt SX_KG ss2 &&
      match sx_statics ss2 with Some ss3 => exit_run_check src0segs src0tbl ss3 code | None => false end
  | None => false
  end.
Definition diag_mf_check (ss : sstate) (msg : list byte) (code : Z) : option Z :=
  match sx_split ss with
  | Some ss2 =>
      if ss_atoms_lt SX_KG ss2 then
        match sx_statics ss2 with Some ss3 => diag_exit_check SX_KD ss3 msg code | None => None end
      else None
  | None => None
  end.

(** ** Soundness *)
Section sound.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma chunk_ok8 : forall E m base off v z,
  sv_denot E v = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 ->
  val_mem src0segs m (base + off) 8 z -> chunk_ok src0segs E m base (mkChunk off (CVal 8 v)).
Proof.
  intros E m base off v z Hv Hz H i Hi. cbn [c_len cv_len c_val c_off] in Hi |- *. change (Z.of_N 8) with 8 in Hi.
  assert (Hk : (Z.to_nat i < 8)%nat) by lia.
  pose proof (H (Z.to_nat i) Hk) as Hb. rewrite Z2Nat.id in Hb by lia.
  exists (Z_to_bv 8 (le_byte z 8 (Z.to_nat i))). split; [|exact Hb].
  cbn [cbyte]. rewrite Hv, byte_of_word_lit. f_equal.
  rewrite le_byte_small; [| change (8 * Z.of_nat 8) with 64; lia | exact Hk].
  unfold zcanon, M64. rewrite Z.mod_small by lia. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma chunk_ok4 : forall E m base off v z,
  sv_denot E v = Z_to_bv 64 z -> 0 <= z < 2 ^ 32 ->
  val_mem src0segs m (base + off) 4 z -> chunk_ok src0segs E m base (mkChunk off (CVal 4 v)).
Proof.
  intros E m base off v z Hv Hz H i Hi. cbn [c_len cv_len c_val c_off] in Hi |- *. change (Z.of_N 4) with 4 in Hi.
  assert (Hk : (Z.to_nat i < 4)%nat) by lia.
  pose proof (H (Z.to_nat i) Hk) as Hb. rewrite Z2Nat.id in Hb by lia.
  exists (Z_to_bv 8 (le_byte z 4 (Z.to_nat i))). split; [|exact Hb].
  cbn [cbyte]. rewrite Hv, byte_of_word_lit. f_equal.
  rewrite le_byte_small; [| change (8 * Z.of_nat 4) with 32; lia | exact Hk].
  unfold zcanon, M64. rewrite Z.mod_small by lia. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma sv_denot_off : forall E n z f, bv_unsigned (ew E n) = f -> sv_denot E (SOff n z) = Z_to_bv 64 (f + z).
Proof. intros E n z f H. cbn [sv_denot]. rewrite H. reflexivity. Qed.

Lemma ms_segs_src0 : ms_segs src0_msyms = src0segs.
Proof. reflexivity. Qed.

(** The FILE block's region lies beside every region [rfx_ok] admits. *)
Lemma rfx_disjoint : forall E F rs kf cs f,
  rfx_ok F rs = true -> stack_anchored E F ->
  bv_unsigned (ew E kf) = f -> f + MF_BLOCK <= alloc_ceiling ->
  (forall i, 0 <= i < MF_BLOCK -> ~ in_img src0_msyms (f + i)) ->
  Forall (extent_disjoint E (rf_region kf cs)) rs.
Proof.
  intros E F rs kf cs f Hck HSA Hkf Hfc Hni. apply Forall_forall. intros r Hr.
  pose proof (forallb_In _ _ r Hck Hr) as Hrr. unfold rfx_region_ok in Hrr.
  unfold extent_disjoint. cbn [rf_region r_base r_lo r_hi base_val]. rewrite Hkf.
  unfold MF_ZEROED, MF_BLOCK in *.
  destruct (r_base r) as [n|] eqn:Hb.
  - destruct (anch_lo F n) as [K|] eqn:HK; [|discriminate]. apply Z.leb_le in Hrr.
    pose proof (stack_anchored_sound E F n K HSA HK). cbn [base_val]. left. lia.
  - cbn [base_val]. apply andb_prop in Hrr as [Hle Hs]. apply Z.leb_le in Hle.
    unfold seg_one in Hs. apply existsb_In in Hs as (s & Hs & Hc).
    apply andb_prop in Hc as [Hc Hpos]. apply andb_prop in Hc as [Hlo Hhi].
    apply Z.leb_le in Hlo. apply Z.leb_le in Hhi. apply Z.ltb_lt in Hpos.
    assert (Himg : forall a, bv_unsigned (fst s) <= a < bv_unsigned (fst s) + bv_unsigned (snd s) ->
      in_img src0_msyms a).
    { intros a Ha. split.
      - intros E0. rewrite ms_segs_src0 in E0. rewrite E0 in Hs. vm_compute in Hs. exact Hs.
      - exists s. rewrite ms_segs_src0. split; [exact Hs | exact Ha]. }
    destruct (Z_le_dec (f + 272) (bv_unsigned (fst s))) as [H1|H1]; [left; lia|].
    destruct (Z_lt_dec f (bv_unsigned (fst s))) as [H2|H2].
    + exfalso. apply (Hni (bv_unsigned (fst s) - f)); [lia|].
      replace (f + (bv_unsigned (fst s) - f)) with (bv_unsigned (fst s)) by lia. apply Himg. lia.
    + destruct (Z_lt_dec f (bv_unsigned (fst s) + bv_unsigned (snd s))) as [H3|H3].
      * exfalso. apply (Hni 0); [lia|]. rewrite Z.add_0_r. apply Himg. lia.
      * right. lia.
Qed.

(** A region with no write window at the head of a well-formed memory: no write window of the memory meets it. *)
Lemma rf_no_wrange : forall E m r rs a, mem_ok src0segs E m (r :: rs) -> r_whi r <= r_wlo r ->
  base_val E (r_base r) + r_lo r <= a < base_val E (r_base r) + r_hi r -> ~ in_wrange E (r :: rs) a.
Proof.
  intros E m r rs a (Hwf & Hok & Hpd) Hw Ha (r' & Hin & Hw').
  destruct Hin as [<-|Hin]; [lia|].
  cbn [pairwise_disjoint] in Hpd. destruct Hpd as [Hall _].
  pose proof (all_disjoint_In E r rs r' Hall Hin) as Hd. unfold extent_disjoint in Hd.
  cbn [regions_wf] in Hwf. apply andb_prop in Hwf as [_ Hwf].
  pose proof (region_wf_facts r' (regions_wf_In rs r' Hwf Hin)) as (Hlh & Hww & _).
  destruct Hww as [Hww|Hww]; lia.
Qed.

Lemma rf_region_ok : forall E m kf f cs,
  bv_unsigned (ew E kf) = f -> 0 <= f -> f + MF_BLOCK <= 2 ^ 64 ->
  Forall (chunk_ok src0segs E m f) cs -> region_ok src0segs E m (rf_region kf cs).
Proof.
  intros E m kf f cs Hkf H0 H1 Hc. unfold region_ok. cbn [rf_region r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
  rewrite Hkf. unfold MF_ZEROED, MF_BLOCK in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia | exact Hc].
Qed.

Lemma sx_addc_ok : forall E ss ms c ss',
  st_ok src0segs E ss ms -> sx_addc ss c = Some ss' -> chunk_ok src0segs E (ms_mem ms) 0 c ->
  st_ok src0segs E ss' ms.
Proof.
  intros E ss ms c ss' HS H Hc. unfold sx_addc in H.
  destruct (YN3u.add_chunk_sem (ss_mem ss) None c) as [[rs' cs]|] eqn:Ha; [|discriminate]. injection H as <-.
  exact (YN3u.st_ok_add_chunk_sem src0segs E ss ms None c rs' cs HS Ha (fun _ => Hc)).
Qed.

Lemma sx_base_ok : forall E s1 ms, st_ok src0segs E s1 ms ->
  relayout_ok src0segs (ss_mem s1) (sx_dropl (ss_facts s1) (same_layout (ss_mem s1))) = true ->
  st_ok src0segs E (sx_base s1) ms.
Proof. intros E s1 ms HS H. exact (st_ok_relayout src0segs E s1 ms _ HS H). Qed.

Lemma sx_addr_ok : forall E ss ms r,
  st_ok src0segs E ss ms -> region_wf r = true -> region_ok src0segs E (ms_mem ms) r ->
  Forall (extent_disjoint E r) (ss_mem ss) -> st_ok src0segs E (sx_addr r ss) ms.
Proof. intros E ss ms r HS Hw Hr Hd. exact (YN2j.st_ok_add_region src0segs E ss ms r HS Hw Hr Hd). Qed.

Lemma head_chunk_ok : forall E m v w, sv_denot E v = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 ->
  word_mem src0segs m OFLH w -> chunk_ok src0segs E m 0 (rf_ch8 OFLH v).
Proof.
  intros E m v w Hv Hw H. apply (chunk_ok8 E m 0 OFLH v w Hv Hw). rewrite Z.add_0_l.
  apply (proj2 (val_mem_word_mem src0segs m OFLH w)). exact H.
Qed.

Lemma said_writable : forall m a, in_globals MW_G a -> writable_at src0segs m a.
Proof.
  intros m a (lo & len & Hin & Ha). destruct Hin as [Hin|[]]. injection Hin as <- <-. cbn [mf_buf mf_size link_mf] in Ha.
  assert (Hz : zallb (img_writable_ok src0segs) 0x74530 (Z.to_nat 4096) = true) by (vm_compute; reflexivity).
  pose proof (zallb_sound _ _ _ a Hz ltac:(rewrite Z2Nat.id by lia; lia)) as Ho. unfold img_writable_ok in Ho.
  unfold writable_at.
  apply (wview_grows src0segs (fun _ => None)); [intros x Hx; exfalso; apply Hx; reflexivity|].
  destruct (wview src0segs (fun _ => None) (Z_to_bv 64 a)); [discriminate | discriminate Ho].
Qed.

(** One state for every arm: an arm's end state [se] (under an environment that agrees with [E] below
    [SX_KF]) gives [sx_ss2]. *)
Lemma sx_canon : forall E E' s1 se ms2 sp_off,
  facts_ok E (ss_facts s1) -> ss_atoms_lt SX_KF s1 = true -> env_agree SX_KF E E' ->
  mem_atoms_lt SX_KF (ss_mem (sx_ss2 sp_off s1)) = true ->
  st_ok src0segs E' se ms2 -> sx_end_ok sp_off s1 se = true ->
  exists E2, st_ok src0segs E2 (sx_ss2 sp_off s1) ms2.
Proof.
  intros E E' s1 se ms2 sp_off HF1 Hat1 HA HM2 HS He.
  unfold sx_end_ok in He.
  apply andb_prop in He as [He Hrl]. apply andb_prop in He as [He Hat]. apply andb_prop in He as [He Hregs].
  apply andb_prop in He as [He Hs0]. apply andb_prop in He as [Hpc Hrv].
  apply Z.eqb_eq in Hpc. apply sv_eqb_eq in Hs0. apply svl_eqb_eq in Hregs.
  destruct (ss_resv se) eqn:Hrv'; [discriminate|].
  pose proof (st_ok_mkst src0segs E' se ms2 HS Hrv') as Hms. rewrite Hpc in Hms.
  assert (HM : mem_ok src0segs E' (ms_mem ms2) (ss_mem (sx_ss2 sp_off s1))).
  { pose proof (mem_ok_relayout src0segs E' (ms_mem ms2) (ss_mem se) _ (st_ok_mem_ok src0segs E' se ms2 HS) Hrl) as H.
    rewrite realign_snd in H. exact H. }
  pose proof (st_ok_regs_ok src0segs E' se ms2 HS 8%bv) as H8. rewrite Hs0 in H8.
  rewrite Hms in HS.
  pose proof (st_ok_splice_havoc src0segs SX_K E' se (ms_regs ms2) (ms_regs ms2) (Z_to_bv 64 SX_CONT) SX_CONT
    (ms_mem ms2) (ms_mem ms2) (ss_mem (sx_ss2 sp_off s1)) [(8%bv, SLit 0)] caller_saved HS Hat
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
    (YN2j.mem_atoms_lt_mono SX_KF SX_K _ ltac:(unfold SX_KF, SX_K; lia) HM2)
    (fun r _ => eq_refl)
    ltac:(constructor; [split; [reflexivity | exact H8] | constructor])
    HM) as HS2.
  change ([(8%bv, SLit 0)] ++ junk_upd SX_K caller_saved) with sx_upd in HS2.
  rewrite Hregs in HS2.
  set (E2 := havoc E' SX_K (map (getr (ms_regs ms2)) caller_saved)) in HS2.
  assert (HA2 : env_agree SX_KF E E2).
  { eapply env_agree_trans; [exact HA|]. eapply env_agree_le; [|apply env_agree_havoc]. unfold SX_KF, SX_K. lia. }
  assert (Hfa1 : facts_atoms_lt SX_KF (ss_facts s1) = true).
  { unfold ss_atoms_lt in Hat1. apply andb_prop in Hat1 as [Hat1 _]. apply andb_prop in Hat1 as [_ Hf]. exact Hf. }
  pose proof (facts_ok_agree SX_KF E E2 (ss_facts s1) HA2 Hfa1 HF1) as HF2.
  pose proof (YN2j.st_ok_rebuild src0segs E2 E2 _ _ _ _ (ss_facts s1) HS2 eq_refl
    (st_ok_regs_ok src0segs _ _ _ HS2) (st_ok_mem_ok src0segs _ _ _ HS2) HF2) as HS3.
  exists E2. rewrite Hms. exact HS3.
Qed.

Lemma rf_pre_ok : forall E m f wpos wbase zp zb,
  memfile_at src0_msyms link_mf m f ->
  sv_denot E wpos = Z_to_bv 64 zp -> 0 <= zp < 2 ^ 64 -> val_mem src0segs m (f + 40) 8 zp ->
  sv_denot E wbase = Z_to_bv 64 zb -> 0 <= zb < 2 ^ 64 -> val_mem src0segs m (f + 56) 8 zb ->
  Forall (chunk_ok src0segs E m f) (rf_pre_chunks wpos wbase).
Proof.
  intros E m f wpos wbase zp zb Hm Hp Hzp Hvp Hb Hzb Hvb.
  destruct (memfile_close_reads src0_msyms link_mf m f Hm) as (Hl & Hw & Hr & Hd & Hn).
  unfold rf_pre_chunks, rf_ch8.
  constructor; [apply (chunk_ok4 E m f 140 (SLit U32M1) U32M1 eq_refl ltac:(unfold U32M1; lia) Hl)|].
  constructor; [apply (chunk_ok8 E m f 72 (SLit (mf_write link_mf)) (mf_write link_mf) eq_refl ltac:(cbn; lia) Hw)|].
  constructor; [apply (chunk_ok8 E m f 8 (SLit 0) 0 eq_refl ltac:(lia) Hr)|].
  constructor; [apply (chunk_ok8 E m f 16 (SLit 0) 0 eq_refl ltac:(lia) Hd)|].
  constructor; [apply (chunk_ok8 E m f 112 (SLit 0) 0 eq_refl ltac:(lia) Hn)|].
  constructor; [apply (chunk_ok8 E m f 40 wpos zp Hp Hzp Hvp)|].
  constructor; [apply (chunk_ok8 E m f 56 wbase zb Hb Hzb Hvb)|].
  constructor.
Qed.

Lemma rf_post_ok : forall E m f, memfile_at src0_msyms link_mf m f ->
  Forall (chunk_ok src0segs E m f) rf_post_chunks.
Proof.
  intros E m f Hm. destruct (memfile_close_reads src0_msyms link_mf m f Hm) as (_ & _ & Hr & Hd & Hn).
  unfold rf_post_chunks, rf_ch8.
  constructor; [apply (chunk_ok8 E m f 8 (SLit 0) 0 eq_refl ltac:(lia) Hr)|].
  constructor; [apply (chunk_ok8 E m f 16 (SLit 0) 0 eq_refl ltac:(lia) Hd)|].
  constructor; [apply (chunk_ok8 E m f 112 (SLit 0) 0 eq_refl ltac:(lia) Hn)|].
  constructor.
Qed.

Lemma sx_addc_cons : forall r ss c sf, r_base r <> None ->
  sx_addc (sx_addr r ss) c = Some sf -> exists rs, ss_mem sf = r :: rs.
Proof.
  intros r ss c sf Hb H. unfold sx_addc, sx_addr in H. cbn [ss_mem YN3u.add_chunk_sem] in H.
  destruct (r_base r) as [n|]; [|exfalso; exact (Hb eq_refl)]. cbn [obase_eqb andb] in H.
  destruct (YN3u.add_chunk_sem (ss_mem ss) None c) as [[rs'' cs]|]; [|discriminate].
  injection H as <-. exists rs''. reflexivity.
Qed.

Lemma ss_atoms_facts : forall k ss, ss_atoms_lt k ss = true -> facts_atoms_lt k (ss_facts ss) = true.
Proof. intros k ss H. unfold ss_atoms_lt in H. apply andb_prop in H as [H _]. apply andb_prop in H as [_ Hf]. exact Hf. Qed.

Lemma mf_head_in_G : forall a, @mf_head_addr src0_sink_head link_mf a -> in_globals src0_G a.
Proof.
  intros a Ha. cbv [mf_head_addr mf_sink_addr mf_say_addr link_mf sk_ofl_head src0_sink_head src0_D_ofl_head] in Ha.
  unfold in_globals, src0_G.
  destruct Ha as [Ha|[Ha|Ha]].
  - exists 0x74528, 8. split; [cbn; tauto | lia].
  - exists 0x75530, 8. split; [cbn; tauto | lia].
  - exists 0x95cc8, 8. split; [cbn; tauto | lia].
Qed.

(** The two-arm exit: from any state [ss] whose split check passes, with the slot's GI conjunct [mf_gi], the
    run reaches 0x199bc in the state [sx_split ss]. *)
Theorem stdio_exit_two_arm : forall (API : AllocAPI src0_msyms),
  AllocExtra src0_msyms (aa_MR API) ->
  forall (md : Model) (RZ : machine_state -> Prop),
  (forall E0 ss0 ss1 ms0 stop, st_ok src0segs E0 ss0 ms0 ->
     run_to_check src0segs src0tbl stop ss0 = Some ss1 ->
     (forall ms1, st_ok src0segs E0 ss1 ms1 -> frame_of E0 (ss_mem ss0) (ms_mem ms0) (ms_mem ms1) -> RZ ms1) ->
     RZ ms0) ->
  (forall L0 A0 regs mem f, mw_pre src0_msyms API SX_MW_RA L0 A0 regs mem md f ->
     (forall regs' mem', mw_post src0_msyms API L0 A0 regs mem md f regs' mem' ->
        RZ (mkst regs' (Z_to_bv 64 SX_MW_RA) mem' (seg_rom src0segs))) ->
     RZ (mkst regs (Z_to_bv 64 (mf_write link_mf)) mem (seg_rom src0segs))) ->
  forall E ss ss2 ms L A T,
  st_ok src0segs E ss ms -> stack_anchored E (ss_facts ss) ->
  sx_split ss = Some ss2 ->
  aa_MR API L A (ms_mem ms) md -> WF A -> bounded A ->
  mf_gi src0_msyms link_mf T (ms_mem ms) -> tb_live L A T ->
  (forall E2 ms2, st_ok src0segs E2 ss2 ms2 -> aa_MR API L A (ms_mem ms2) md -> RZ ms2) ->
  RZ ms.
Proof.
  intros API AX md RZ HRT HMW E ss ss2 ms L A T HS HSA Hsp HMR HW HB HGI HTL K.
  unfold sx_split in Hsp.
  destruct (run_to_check src0segs src0tbl SX_HEAD_LD ss) as [s1|] eqn:Hr1; [|discriminate].
  set (sp_off := sx_sp_off s1) in Hsp.
  match type of Hsp with (if ?c then _ else _) = _ => destruct c eqn:Hck; [|discriminate] end.
  injection Hsp as <-.
  apply andb_prop in Hck as [Hck Hak]. apply andb_prop in Hck as [Hck Haf2]. apply andb_prop in Hck as [Hck Haf1].
  apply andb_prop in Hck as [Hck Ha0]. apply andb_prop in Hck as [Hck Hrlb]. apply andb_prop in Hck as [Hck Hrfx].
  apply andb_prop in Hck as [Hck HM2]. apply andb_prop in Hck as [Hck Hanlt]. apply andb_prop in Hck as [Hck Hanc1].
  apply andb_prop in Hck as [Hck Hat1b]. apply andb_prop in Hck as [Hck Hat1]. apply andb_prop in Hck as [Hck Ha10]. apply andb_prop in Hck as [Hck Hrv1].
  apply andb_prop in Hck as [Hgwr Hwr].
  apply sv_eqb_eq in Ha10. apply anch_eqb_eq in Hanc1.
  destruct (ss_resv s1) eqn:Hrv1'; [discriminate|].
  pose proof (st_ok_facts_ok src0segs E ss ms HS) as HG.
  apply (HRT E ss s1 ms SX_HEAD_LD HS Hr1). intros ms1 HS1 HF1.
  pose proof (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX L A (ms_mem ms) (ms_mem ms1) md E (ss_facts ss)
    src0_keep (ss_mem ss) HMR HG HSA Hwr HF1) as HMR1.
  pose proof (GI_frame_T src0_msyms (aa_MR API) (aa_laws API) AX src0_G (fun _ T m => mf_gi src0_msyms link_mf T m)
    (mf_gi_local src0_msyms link_mf src0_G mf_head_in_G) src0_keep 0%nat T L A md (ms_mem ms) (ms_mem ms1) E
    (ss_facts ss) (ss_mem ss) HGI HTL HMR HG HSA Hgwr Hwr HF1) as HGI1. cbv beta in HGI1.
  pose proof (st_ok_facts_ok src0segs E s1 ms1 HS1) as HF1s.
  assert (HSA1 : stack_anchored E (ss_facts s1)).
  { eapply stack_anchored_ext; [exact HSA | exact Hanc1 | intros a _; reflexivity]. }
  pose proof (sx_base_ok E s1 ms1 HS1 Hrlb) as HSb.
  destruct HGI1 as [(H0 & ->) | (f & Hf & -> & Hmf)].
  - (* head 0: the released walk *)
    unfold sx_arm_ok in Ha0. destruct (sx_arm0 s1) as [sa|] eqn:Hsa; [|discriminate].
    apply andb_prop in Ha0 as [Hwa Ha0]. apply andb_prop in Hwa as [Hwra Hana]. apply anch_eqb_eq in Hana.
    destruct (run_to_check src0segs src0tbl SX_CONT sa) as [se|] eqn:Hse; [|discriminate].
    assert (HSa : st_ok src0segs E sa ms1).
    { apply (sx_addc_ok E (sx_base s1) ms1 (rf_ch8 OFLH (SLit 0)) sa HSb Hsa).
      apply (head_chunk_ok E (ms_mem ms1) (SLit 0) 0 eq_refl ltac:(lia)).
      exact (mf_heads_ofl src0_msyms link_mf (ms_mem ms1) 0 H0). }
    apply (HRT E sa se ms1 SX_CONT HSa Hse). intros ms2 HS2 HF2.
    pose proof (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX L A (ms_mem ms1) (ms_mem ms2) md E
      (ss_facts sa) src0_keep (ss_mem sa) HMR1 (st_ok_facts_ok src0segs E sa ms1 HSa)
      (stack_anchored_ext E E _ _ HSA Hana (fun _ _ => eq_refl)) Hwra HF2) as HMR2.
    destruct (sx_canon E E s1 se ms2 sp_off HF1s Hat1 (env_agree_refl SX_KF E) HM2 HS2 Ha0) as (E2 & HS3).
    exact (K E2 ms2 HS3 HMR2).
  - (* head f: the FILE's close_file *)
    assert (HinB : In (f, MF_BLOCK) (blocks L A)) by (destruct HTL as [_ HTL]; apply HTL; left; reflexivity).
    unfold blocks in HinB. apply in_map_iff in HinB as ((q & n0) & Hq & HinA). cbn [fst snd] in Hq. injection Hq as Hqf Hn0.
    subst n0.
    destruct (mr_blocks_range src0_msyms (aa_MR API) (aa_laws API) L A (ms_mem ms1) md q MF_BLOCK HMR1 HinA) as [Hf4 Hfc].
    rewrite Hqf in Hf4, Hfc.
    assert (Hni : forall i, 0 <= i < MF_BLOCK -> ~ in_img src0_msyms (f + i)).
    { intros i Hi. rewrite <- Hqf. exact (ax_blocks_img AX L A (ms_mem ms1) md q MF_BLOCK i HMR1 HinA Hi). }
    pose proof alloc_ceiling_value as [[Hcmin Hcmax] _].
    pose proof Hmf as (Hf0 & Hf1 & Hf2 & _ & _ & _ & Hwin & _).
    destruct (memfile_close_reads src0_msyms link_mf (ms_mem ms1) f Hmf) as (Hlock & Hwrite & Hrpos & Hrend & Hnext).
    assert (Hfw : 0 <= f < 2 ^ 64) by (unfold MF_BLOCK in *; lia).
    assert (Hhead : word_mem src0segs (ms_mem ms1) OFLH f) by exact (mf_heads_ofl src0_msyms link_mf (ms_mem ms1) f Hf).
    (* the environment with the FILE's atom (and, for a non-empty window, its [wpos]) *)
    assert (Hfat : forall E1, bv_unsigned (ew E1 SX_KF) = f -> afact_ok E1 SX_KF sx_fatom).
    { intros E1 H1. unfold afact_ok, sx_fatom. cbn [af_lo af_hi af_al2]. rewrite H1. unfold MF_BLOCK in *.
      split; [lia|]. split; [|lia]. change (2 ^ 4) with 16. exact Hf2. }
    assert (HinB' : In (f, MF_BLOCK) (blocks L A)).
    { unfold blocks. apply in_map_iff. exists (q, MF_BLOCK). cbn [fst snd]. rewrite Hqf. split; [reflexivity | exact HinA]. }
    pose proof (ss_atoms_facts SX_KF s1 Hat1) as Hfa1.
    (* every arm: the environment with the FILE's atom [SX_KF] and the window's [wpos] atom [SX_KW] *)
    assert (Hbase : forall w, let E1 := ewset (ewset E SX_KF (Z_to_bv 64 f)) SX_KW w in
      env_agree SX_KF E E1 /\ bv_unsigned (ew E1 SX_KF) = f /\ stack_anchored E1 (ss_facts s1) /\
      st_ok src0segs E1 (add_atom (sx_base s1) SX_KF sx_fatom) ms1).
    { intros w E1.
      assert (HA1 : env_agree SX_KF E E1) by apply env_agree_ewset2.
      assert (HK1 : bv_unsigned (ew E1 SX_KF) = f).
      { subst E1. rewrite ew_ewset_other by (unfold SX_KF, SX_KW; lia). rewrite ew_ewset_same. apply lit64_small. exact Hfw. }
      split; [exact HA1|]. split; [exact HK1|]. split.
      - exact (stack_anchored_agree SX_KF E E1 (ss_facts s1) HA1 Hfa1 HSA1).
      - apply (st_ok_add_fact src0segs E1 _ ms1 SX_KF sx_fatom); [|exact (Hfat E1 HK1)].
        exact (st_ok_agree src0segs SX_KF E E1 _ ms1 HSb HA1 Hat1b). }
    assert (Hhead1 : forall E1, bv_unsigned (ew E1 SX_KF) = f ->
      chunk_ok src0segs E1 (ms_mem ms1) 0 (rf_ch8 OFLH (SOff SX_KF 0))).
    { intros E1 H1. apply (head_chunk_ok E1 (ms_mem ms1) (SOff SX_KF 0) f); [|exact Hfw | exact Hhead].
      rewrite (sv_denot_off E1 SX_KF 0 f H1). rewrite Z.add_0_r. reflexivity. }
    assert (Hdisj : forall E1 cs, stack_anchored E1 (ss_facts s1) -> bv_unsigned (ew E1 SX_KF) = f ->
      Forall (extent_disjoint E1 (rf_region SX_KF cs)) (ss_mem (sx_base s1))).
    { intros E1 cs HSA' H1. exact (rfx_disjoint E1 (ss_facts s1) _ SX_KF cs f Hrfx HSA' H1 Hfc Hni). }
    (* the FILE's and the window's atoms are above every anchored atom of the exit *)
    assert (Hanc_gen : forall w a, In a (anchored_atoms (ss_facts ss)) ->
      ew (ewset (ewset E SX_KF (Z_to_bv 64 f)) SX_KW w) (fst a) = ew E (fst a)).
    { intros w a Ha. pose proof (forallb_In _ _ a Hanlt Ha) as Hlt. cbn beta in Hlt. apply Nat.ltb_lt in Hlt.
      rewrite !ew_ewset_other by (unfold SX_KF, SX_KW in *; lia). reflexivity. }
    (* the two arms that call nothing: run to 0x199bc *)
    assert (Hnocall : forall wpos wbase zp zb,
      sx_arm_ok sp_off ss s1 (sx_armf s1 wpos wbase) = true ->
      (forall E1, bv_unsigned (ew E1 SX_KF) = f ->
         sv_denot E1 wpos = Z_to_bv 64 zp /\ sv_denot E1 wbase = Z_to_bv 64 zb) ->
      0 <= zp < 2 ^ 64 -> val_mem src0segs (ms_mem ms1) (f + 40) 8 zp ->
      0 <= zb < 2 ^ 64 -> val_mem src0segs (ms_mem ms1) (f + 56) 8 zb ->
      RZ ms1).
    { intros wpos wbase zp zb Harm Hden Hzp Hvp Hzb Hvb.
      destruct (Hbase (Z_to_bv 64 0)) as (HA1 & HK1 & HSA' & HS').
      set (E1 := ewset (ewset E SX_KF (Z_to_bv 64 f)) SX_KW (Z_to_bv 64 0)) in *.
      destruct (Hden E1 HK1) as [Hdp Hdb].
      unfold sx_arm_ok in Harm. destruct (sx_armf s1 wpos wbase) as [sf|] eqn:Hsf; [|discriminate].
      apply andb_prop in Harm as [Hwa Harm]. apply andb_prop in Hwa as [Hwrf Hanf]. apply anch_eqb_eq in Hanf.
      destruct (run_to_check src0segs src0tbl SX_CONT sf) as [se|] eqn:Hse; [|discriminate].
      assert (HSf : st_ok src0segs E1 sf ms1).
      { unfold sx_armf in Hsf. eapply (sx_addc_ok E1 _ ms1 _ sf); [| exact Hsf | exact (Hhead1 E1 HK1)].
        apply sx_addr_ok; [exact HS' | reflexivity | |].
        - apply (rf_region_ok E1 (ms_mem ms1) SX_KF f); [exact HK1 | lia | unfold MF_BLOCK in *; lia |].
          exact (rf_pre_ok E1 (ms_mem ms1) f wpos wbase zp zb Hmf Hdp Hzp Hvp Hdb Hzb Hvb).
        - exact (Hdisj E1 _ HSA' HK1). }
      apply (HRT E1 sf se ms1 SX_CONT HSf Hse). intros ms2 HS2 HF2.
      pose proof (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX L A (ms_mem ms1) (ms_mem ms2) md E1
        (ss_facts sf) src0_keep (ss_mem sf) HMR1 (st_ok_facts_ok src0segs E1 sf ms1 HSf)
        (stack_anchored_ext E E1 _ _ HSA Hanf (Hanc_gen (Z_to_bv 64 0))) Hwrf HF2) as HMR2.
      destruct (sx_canon E E1 s1 se ms2 sp_off HF1s Hat1 HA1 HM2 HS2 Harm) as (E2 & HS3).
      exact (K E2 ms2 HS3 HMR2). }
    destruct Hwin as (_ & _ & [(Hwe & Hwp & Hwb) | (k & Hk & Hwe & Hwp & Hwb)]).
    + (* window empty *)
      apply (Hnocall (SLit 0) (SLit 0) 0 0 Haf1); [intros; split; reflexivity | lia | exact Hwp | lia | exact Hwb].
    + destruct (Z.eq_dec k 0) as [-> | Hk0].
      * (* window active, no byte pending *)
        rewrite Z.add_0_r in Hwp.
        apply (Hnocall (SOff SX_KF 280) (SOff SX_KF 280) (f + MF_BUF) (f + MF_BUF) Haf2).
        -- intros E1 H1. rewrite (sv_denot_off E1 SX_KF 280 f H1). split; reflexivity.
        -- unfold MF_BUF, MF_BLOCK in *; lia.
        -- exact Hwp.
        -- unfold MF_BUF, MF_BLOCK in *; lia.
        -- exact Hwb.
      * (* window active with bytes: f->write = mwrite *)
        assert (Hk1 : 0 < k <= MF_BUFSIZ) by lia.
        destruct (Hbase (Z_to_bv 64 (f + MF_BUF + k))) as (HA1 & HK1 & HSA' & HS').
        set (E1 := ewset (ewset E SX_KF (Z_to_bv 64 f)) SX_KW (Z_to_bv 64 (f + MF_BUF + k))) in *.
        assert (HKW : bv_unsigned (ew E1 SX_KW) = f + MF_BUF + k).
        { subst E1. rewrite ew_ewset_same. apply lit64_small. unfold MF_BUF, MF_BUFSIZ, MF_BLOCK in *. lia. }
        unfold sx_armk_ok in Hak. destruct (sx_armk s1) as [sf|] eqn:Hsf; [|discriminate].
        destruct (run_to_check src0segs src0tbl (mf_write link_mf) sf) as [sc|] eqn:Hsc; [|discriminate].
        apply andb_prop in Hak as [Hak Hret]. apply andb_prop in Hak as [Hcall Hwrr].
        destruct (run_to_check src0segs src0tbl SX_CONT (sx_ret sp_off sc)) as [se|] eqn:Hse; [|discriminate].
        assert (HSf : st_ok src0segs E1 sf ms1).
        { unfold sx_armk in Hsf. eapply (sx_addc_ok E1 _ ms1 _ sf); [| exact Hsf | exact (Hhead1 E1 HK1)].
          apply sx_addr_ok; [| reflexivity | |].
          - apply (st_ok_add_cond_neg src0segs E1 _ ms1 BC_EQ (SOff SX_KW 0) (SOff SX_KF 280) HS').
            cbn [branch_taken]. rewrite (sv_denot_off E1 SX_KW 0 _ HKW), (sv_denot_off E1 SX_KF 280 f HK1).
            apply bv_eqb_false_iff. intros Heq. apply (f_equal bv_unsigned) in Heq.
            rewrite !lit64_small in Heq by (unfold MF_BUF, MF_BUFSIZ, MF_BLOCK in *; lia).
            unfold MF_BUF in *; lia.
          - apply (rf_region_ok E1 (ms_mem ms1) SX_KF f); [exact HK1 | lia | unfold MF_BLOCK in *; lia |].
            apply (rf_pre_ok E1 (ms_mem ms1) f (SOff SX_KW 0) (SOff SX_KF 280) (f + MF_BUF + k) (f + MF_BUF) Hmf).
            + rewrite (sv_denot_off E1 SX_KW 0 _ HKW). rewrite Z.add_0_r. reflexivity.
            + unfold MF_BUF, MF_BUFSIZ, MF_BLOCK in *; lia.
            + exact Hwp.
            + exact (sv_denot_off E1 SX_KF 280 f HK1).
            + unfold MF_BUF, MF_BLOCK in *; lia.
            + exact Hwb.
          - exact (Hdisj E1 _ HSA' HK1). }
        unfold sx_call_ok in Hcall.
        apply andb_prop in Hcall as [Hcall Hro1]. apply andb_prop in Hcall as [Hcall Hrfx1]. apply andb_prop in Hcall as [Hcall Hcf1].
        apply andb_prop in Hcall as [Hcall Hma1]. apply andb_prop in Hcall as [Hcall Hat3].
        apply andb_prop in Hcall as [Hcall Hrl1]. apply andb_prop in Hcall as [Hcall Herr].
        apply andb_prop in Hcall as [Hcall Hka]. apply andb_prop in Hcall as [Hcall Hkc].
        apply andb_prop in Hcall as [Hcall Hanc]. apply andb_prop in Hcall as [Hcall Hanf].
        apply andb_prop in Hcall as [Hcall Hwrf]. apply andb_prop in Hcall as [Hcall Hmwc].
        apply andb_prop in Hcall as [Hpcc Hrvc].
        apply Z.eqb_eq in Hpcc. apply anch_eqb_eq in Hanc. apply anch_eqb_eq in Hanf. apply Z.leb_le in Herr.
        destruct (ss_resv sc) eqn:Hrvc'; [discriminate|].
        assert (Hanc_ew : forall a, In a (anchored_atoms (ss_facts ss)) -> ew E1 (fst a) = ew E (fst a))
          by exact (Hanc_gen (Z_to_bv 64 (f + MF_BUF + k))).
        assert (HSAf : stack_anchored E1 (ss_facts sf)) by exact (stack_anchored_ext E E1 _ _ HSA Hanf Hanc_ew).
        assert (HSAc : stack_anchored E1 (ss_facts sc)) by exact (stack_anchored_ext E E1 _ _ HSA Hanc Hanc_ew).
        apply (HRT E1 sf sc ms1 (mf_write link_mf) HSf Hsc). intros msc HSc HFc.
        pose proof (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX L A (ms_mem ms1) (ms_mem msc) md E1
          (ss_facts sf) src0_keep (ss_mem sf) HMR1 (st_ok_facts_ok src0segs E1 sf ms1 HSf) HSAf Hwrf HFc) as HMRc.
        assert (Hmfc : memfile_at src0_msyms link_mf (ms_mem msc) f).
        { apply (memfile_at_frame src0_msyms link_mf (ms_mem ms1) (ms_mem msc) f); [|exact Hmf].
          unfold sx_armk in Hsf. destruct (sx_addc_cons (rf_region SX_KF (rf_pre_chunks (SOff SX_KW 0) (SOff SX_KF 280))) _ _ sf
            ltac:(cbn; discriminate) Hsf) as (rs & Hrs).
          pose proof (st_ok_mem_ok src0segs E1 sf ms1 HSf) as HMf. rewrite Hrs in HMf.
          intros x Hx. unfold mbyte. rewrite (HFc (Z_to_bv 64 x)); [reflexivity|].
          rewrite lit64_small by (unfold MF_ZEROED, MF_BLOCK in *; lia). rewrite Hrs.
          apply (rf_no_wrange E1 (ms_mem ms1) _ rs x HMf); cbn [rf_region r_whi r_wlo r_base r_lo r_hi base_val];
            [lia | rewrite HK1; unfold MF_ZEROED in *; lia]. }
        pose proof (st_ok_mkst src0segs E1 sc msc HSc Hrvc') as Hmsc. rewrite Hpcc in Hmsc.
        destruct (mw_pre_intro src0_msyms E1 sc msc sp_off SX_KF f HSc HSAc Hmwc
          ltac:(subst E1; rewrite ew_ewset_other by (unfold SX_KF, SX_KW; lia); rewrite ew_ewset_same; reflexivity) Hfw)
          as (Hra & H16 & Hsplo & Hsphi & Hstk & Htp & Herrw & Ha0' & Ha1 & Ha2 & Hsp).
        assert (Hpre : mw_pre src0_msyms API SX_MW_RA L A (ms_regs msc) (ms_mem msc) md f).
        { unfold mw_pre. repeat (split; [assumption|]).
          split; [intros a Ha; exact (said_writable (ms_mem msc) a Ha)|].
          destruct HSc as (_ & _ & _ & _ & _ & _ & _ & HMc & _).
          exact (ro_check_sound src0_msyms E1 (ms_mem msc) (ss_mem sc) (proj1 (proj2 HMc)) Hro1). }
        rewrite Hmsc.
        apply (HMW L A (ms_regs msc) (ms_mem msc) f Hpre).
        intros regs' mem' Hpost.
        rewrite Hmsc in HSc.
        assert (Herr' : errno_addr src0_msyms + 4 <= alloc_ceiling) by lia.
        pose proof (st_ok_after_mw src0_msyms API SX_K3 E1 sc (ms_regs msc) _ (ms_mem msc) md L A f regs' mem' sp_off
          src0_keepG [] (sx_l1 sp_off sc) HSc HSAc Hat3 Hpost Hkc Hka Herr' Hsp ltac:(unfold spZ in Hsplo; lia)
          (fun n sz H => match H with end) Hrl1 Hma1 Hcf1) as HSr0.
        set (E3 := havoc E1 SX_K3 (map (getr regs') caller_saved)) in HSr0.
        assert (HA3 : env_agree SX_K3 E1 E3) by apply env_agree_havoc.
        assert (HK3 : bv_unsigned (ew E3 SX_KF) = f).
        { destruct HA3 as [HA3 _]. rewrite HA3 by (unfold SX_KF, SX_K3; lia). exact HK1. }
        assert (HSA3 : stack_anchored E3 (ss_facts sc)).
        { exact (stack_anchored_agree SX_K3 E1 E3 (ss_facts sc) HA3 (ss_atoms_facts SX_K3 sc Hat3) HSAc). }
        assert (HSr : st_ok src0segs E3 (sx_ret sp_off sc) (mkst regs' (Z_to_bv 64 SX_MW_RA) mem' (seg_rom src0segs))).
        { unfold sx_ret. apply sx_addr_ok; [exact HSr0 | reflexivity | |].
          - apply (rf_region_ok E3 mem' SX_KF f); [exact HK3 | lia | unfold MF_BLOCK in *; lia |].
            destruct Hpost as (_ & _ & _ & _ & _ & _ & _ & Hmf'). exact (rf_post_ok E3 mem' f Hmf').
          - exact (rfx_disjoint E3 (ss_facts sc) _ SX_KF rf_post_chunks f Hrfx1 HSA3 HK3 Hfc Hni). }
        apply (HRT E3 (sx_ret sp_off sc) se _ SX_CONT HSr Hse). intros ms2 HS2 HF2.
        pose proof (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX L A _ (ms_mem ms2) md E3
          (ss_facts (sx_ret sp_off sc)) src0_keep (ss_mem (sx_ret sp_off sc)) (proj1 Hpost)
          (st_ok_facts_ok src0segs E3 _ _ HSr) HSA3 Hwrr HF2) as HMR2.
        assert (HA13 : env_agree SX_KF E E3).
        { eapply env_agree_trans; [exact HA1|]. eapply env_agree_le; [|exact HA3]. unfold SX_KF, SX_K3. lia. }
        destruct (sx_canon E E3 s1 se ms2 sp_off HF1s Hat1 HA13 HM2 HS2 Hret) as (E2 & HS3).
        exact (K E2 ms2 HS3 HMR2).
Qed.
End sound.

(** ** The slot's [G] in the image, and the two facts the exit sites need beside [mf_gi] *)
Section gimg.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Definition plain_ivl_b (lo hi : Z) : bool :=
  existsb (fun s => (bv_unsigned (fst s) <=? lo) && (hi <=? bv_unsigned (fst s) + bv_unsigned (snd s)))
    (segments_reserved src0segs) &&
  forallb (fun q => (hi <=? fst q) || (snd q <=? lo)) (forbidden_ivl src0_msyms) &&
  forallb (fun q => (hi <=? fst q) || (snd q <=? lo)) (static_ivl src0_msyms) &&
  (hi <=? CEIL_MIN).

Lemma plain_ivl_sound : forall lo hi a, plain_ivl_b lo hi = true -> lo <= a < hi ->
  in_img src0_msyms a /\ ~ static_owned src0_msyms a /\ ~ (ms_ctx src0_msyms <= a < ms_ctx src0_msyms + CTX_SIZE) /\
  ~ (errno_addr src0_msyms <= a < errno_addr src0_msyms + 4) /\ a < CEIL_MIN.
Proof.
  intros lo hi a H Ha. unfold plain_ivl_b in H.
  apply andb_prop in H as [H Hc]. apply andb_prop in H as [H Hst]. apply andb_prop in H as [Hs Hfb].
  apply Z.leb_le in Hc.
  assert (Hout : forall l, forallb (fun q => (hi <=? fst q) || (snd q <=? lo)) l = true ->
    forall q, In q l -> ~ (fst q <= a < snd q)).
  { intros l Hl q Hq Haq. pose proof (forallb_In _ _ q Hl Hq) as D. cbn beta in D.
    apply orb_prop in D as [D|D]; apply Z.leb_le in D; lia. }
  assert (Himg : in_img src0_msyms a).
  { apply existsb_In in Hs as (sg & Hsg & Hin). apply andb_prop in Hin as [S1 S2].
    apply Z.leb_le in S1. apply Z.leb_le in S2. split.
    - intros E0. change (ms_segs src0_msyms) with src0segs in E0. rewrite E0 in Hsg. vm_compute in Hsg. exact Hsg.
    - exists sg. change (ms_segs src0_msyms) with src0segs. split; [exact Hsg | lia]. }
  pose proof (Hout _ Hst) as Hst'. pose proof (Hout _ Hfb) as Hfb'.
  unfold static_ivl in Hst'. unfold forbidden_ivl in Hfb'.
  pose proof (Hst' (ms_lock src0_msyms, ms_lock src0_msyms + 4) ltac:(cbn [In]; tauto)) as A1.
  pose proof (Hst' (ms_libc src0_msyms + 3, ms_libc src0_msyms + 4) ltac:(cbn [In]; tauto)) as A2.
  pose proof (Hst' (ms_libc src0_msyms + 8, ms_libc src0_msyms + 16) ltac:(cbn [In]; tauto)) as A3.
  pose proof (Hst' (ms_libc src0_msyms + 48, ms_libc src0_msyms + 56) ltac:(cbn [In]; tauto)) as A4.
  pose proof (Hst' (ms_got_guard src0_msyms, ms_got_guard src0_msyms + 8) ltac:(cbn [In]; tauto)) as A5.
  pose proof (Hst' (ms_guard src0_msyms, ms_guard src0_msyms + 8) ltac:(cbn [In]; tauto)) as A6.
  pose proof (Hst' (ms_debruijn src0_msyms - 108, ms_debruijn src0_msyms + Z.max 32 (ms_debruijn_len src0_msyms))
    ltac:(cbn [In]; tauto)) as A7.
  pose proof (Hst' (ms_size_classes src0_msyms, ms_size_classes src0_msyms + 96) ltac:(cbn [In]; tauto)) as A8.
  pose proof (Hst' (ms_small_cnt src0_msyms, ms_small_cnt src0_msyms + 27) ltac:(cbn [In]; tauto)) as A9.
  pose proof (Hst' (ms_med_cnt src0_msyms, ms_med_cnt src0_msyms + 4) ltac:(cbn [In]; tauto)) as A10.
  pose proof (Hfb' (vml_lo src0_msyms, vml_lo src0_msyms + vml_len src0_msyms) ltac:(cbn [In]; tauto)) as B1.
  pose proof (Hfb' (ms_ctx src0_msyms, ms_ctx src0_msyms + CTX_SIZE) ltac:(cbn [In]; tauto)) as B2.
  pose proof (Hfb' (errno_addr src0_msyms, errno_addr src0_msyms + 4) ltac:(cbn [In]; tauto)) as B3.
  cbn [fst snd] in A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, B1, B2, B3.
  split; [exact Himg|]. split; [unfold static_owned; lia|].
  split; [lia|]. split; [lia | lia].
Qed.

Lemma src0_G_img : forall a, in_globals src0_G a ->
  in_img src0_msyms a /\ ~ static_owned src0_msyms a /\ ~ (ms_ctx src0_msyms <= a < ms_ctx src0_msyms + CTX_SIZE) /\
  ~ (errno_addr src0_msyms <= a < errno_addr src0_msyms + 4) /\ a < CEIL_MIN.
Proof.
  intros a (lo & len & Hin & Ha).
  assert (H : forallb (fun p => plain_ivl_b (fst p) (fst p + snd p)) src0_G = true) by (vm_compute; reflexivity).
  exact (plain_ivl_sound lo (lo + len) a (forallb_In _ _ (lo, len) H Hin) Ha).
Qed.

(** The two stdio words of [closed_stdio_env] are image bytes outside [G], so the image check that YL0t's
    [src0_env_rom] runs on the whole [env_addr] set holds for them alone after a library call. *)
Definition cenv_check (rs : smem) : bool :=
  sub_ivl (cimg_ivl rs) (@sk_threaded src0_sink) (@sk_threaded src0_sink + 1) &&
  sub_ivl (cimg_ivl rs) (@sk_ofl_lock src0_sink) (@sk_ofl_lock src0_sink + 4).

Lemma cenv_rom : forall E ss ms, st_ok src0segs E ss ms -> cenv_check (ss_mem ss) = true ->
  closed_stdio_env src0_msyms (ms_mem ms).
Proof.
  intros E ss ms HS Hck. unfold cenv_check in Hck. apply andb_prop in Hck as [Ht Hl].
  pose proof (proj1 (proj2 (st_ok_mem_ok src0segs E ss ms HS))) as HF.
  assert (R : forall lo hi, sub_ivl (cimg_ivl (ss_mem ss)) lo hi = true -> forall a, lo <= a < hi ->
    mbyte src0segs (ms_mem ms) a = seg_rom src0segs (Z_to_bv 64 a)).
  { intros lo hi Hsub a Ha. apply (cimg_ivl_sound src0segs E (ms_mem ms) (ss_mem ss) a HF).
    exact (sub_ivl_sound _ _ _ a Hsub Ha). }
  split; intros k Hk;
    [ assert (Hk0 : k = 0%nat) by lia; subst k
    | destruct k as [|[|[|[|k]]]]; try lia ];
    (etransitivity;
     [ first [ solve [apply (R _ _ Ht); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]
             | solve [apply (R _ _ Hl); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia] ]
     | vm_compute; reflexivity ]).
Qed.

(** The slot's [mf_sink] at a call site with [j >= 1]: from the GI conjunct the previous call left. *)
Lemma mf_sink_of_gi_site : forall T mem md,
  mf_gi src0_msyms link_mf T mem -> closed_stdio_env src0_msyms mem ->
  Namei.fd_names_path (m_fds md) sink_path = false ->
  @mf_sink src0_msyms src0_sink_head src0_sink link_mf mem md.
Proof. intros T mem md HG He Hn. exact (mf_sink_of_gi src0_msyms link_mf T mem md HG He Hn). Qed.

End gimg.

(** ** The free site, with the slot's globals kept

    [free_site] (YL0d.v) hides the image clause of [call_post]; the exits after the last library call need it,
    because the heads of [mf_gi] are image bytes below the allocation ceiling. This is [free_site] with that
    one clause added to its continuation. *)
Section fg.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable API : AllocAPI src0_msyms.
Hypothesis AX : AllocExtra src0_msyms (aa_MR API).

Theorem free_site_G : forall E ss ms md L A p n sp_off keep blks k l1 rs2 ra T,
  st_ok src0segs E ss ms -> stack_anchored E (ss_facts ss) ->
  site_check src0_msyms ss (ms_free src0_msyms) ra sp_off keep blks k l1 = true ->
  drv_add_statics src0_msyms (map snd l1) (k + 16) = Some rs2 ->
  aa_MR API L A (ms_mem ms) md -> WF A -> bounded A -> st_init_done A = true ->
  In (p, n) (user_blocks A) ->
  getr (ms_regs ms) 10%bv = Z_to_bv 64 (ptr_addr L p) ->
  (forall kb sz, In (kb, sz) blks -> exists q, In (q, sz) (user_blocks A) /\ ptr_addr L q = bv_unsigned (ew E kb) /\ q <> p) ->
  (forall A' L' ms' md' g tr,
     st_ok src0segs (post_env E k (ms_regs ms') g) (post_state ss ra k rs2) ms' ->
     stack_anchored (post_env E k (ms_regs ms') g) (ss_facts ss) ->
     aa_MR API L' A' (ms_mem ms') md' -> WF A' -> bounded A' ->
     (exists vm', md' = with_vmmaps vm' md) ->
     cpath (free (Some p) A) tr (tt, A') ->
     (exists b1 b2, user_blocks A = b1 ++ (p, n) :: b2 /\ user_blocks A' = b1 ++ b2) ->
     (forall q sz, In (q, sz) (user_blocks A) -> q <> p -> In (q, sz) (user_blocks A') /\ ptr_addr L' q = ptr_addr L q) ->
     (forall a, alloc_ceiling <= a -> a < 2 ^ 64 ->
        ~ (bv_unsigned (ew E 0) + sp_off - ALLOC_STACK <= a < bv_unsigned (ew E 0) + sp_off) ->
        mbyte src0segs (ms_mem ms') a = mbyte src0segs (ms_mem ms) a) ->
     (forall q sz i, In (q, sz) (user_blocks A) -> q <> p -> 0 <= i < sz ->
        mbyte src0segs (ms_mem ms') (ptr_addr L q + i) = mbyte src0segs (ms_mem ms) (ptr_addr L q + i)) ->
     (forall a, in_globals src0_G a -> mbyte src0segs (ms_mem ms') a = mbyte src0segs (ms_mem ms) a) ->
     realizes src0segs (mkCfg ms' md') T) ->
  realizes src0segs (mkCfg ms md) T.
Proof.
  intros E ss ms md L A p n sp_off keep blks k l1 rs2 ra T HS HSA Hck Hrs2 HMR HW HB Hid Hin Ha0 Hblks HK.
  destruct (site_check_sound src0_msyms _ _ _ _ _ _ _ _ Hck) as (Hpc & Hra & Hrv & Hcp & _).
  pose proof (st_ok_mkst src0segs E ss ms HS Hrv) as Hshape.
  destruct (call_pre_intro src0_msyms (aa_MR API) E ss ms L A md sp_off HS HSA HMR HW HB
    ltac:(intros Hf; rewrite Hid in Hf; discriminate) Hcp) as (Hpre & Hsp & Hsplo).
  rewrite Hshape in HS |- *. rewrite Hpc in HS |- *. cbn [ms_regs ms_mem mkst] in *.
  apply (SR_realizes src0segs _ _ T
    (free_SR src0_msyms (aa_MR API) (aa_free API) L A (ms_regs ms) (ms_mem ms) md p n Hpre Hin Ha0)).
  intros c' ([[] A'] & tr & Hpath & (L' & regs' & mem' & md' & -> & Hpost & Hub)). cbn [fst snd] in Hub.
  destruct (free_post src0_msyms API AX E ss ms md L A p n sp_off keep blks k l1 rs2 ra regs' mem' md' L' A'
    HS HSA Hck Hrs2 HMR Hin Hsp Hsplo Hblks Hpost Hub)
    as (g & HS2 & HSA2 & HMR' & HW' & HB' & Hvm & Hkeep & Hhi & Hbk).
  pose proof Hpost as (_ & _ & _ & _ & _ & _ & _ & Himg & _).
  pose proof alloc_ceiling_value as [[Hcmin _] _].
  apply (HK A' L' (mkst regs' (getr (ms_regs ms) 1%bv) mem' (seg_rom src0segs)) md' g tr
    HS2 HSA2 HMR' HW' HB' Hvm Hpath Hub Hkeep Hhi Hbk).
  cbn [ms_mem mkst]. intros a Ha.
  destruct (src0_G_img a Ha) as (Hi & Hst & Hctx & Herr & Hlt).
  assert (Hno : forall L0 A0 m0 d0, aa_MR API L0 A0 m0 d0 -> ~ owned src0_msyms L0 A0 a).
  { intros L0 A0 m0 d0 H0 [Hal|Hso]; [exact (Hctx (ax_img AX L0 A0 m0 d0 a H0 Hi Hal)) | exact (Hst Hso)]. }
  apply (proj1 (Himg a (or_intror Hi) (Hno _ _ _ _ HMR) (Hno _ _ _ _ HMR')
    ltac:(intros [Hs|Hs]; [unfold spZ in Hs; lia | exact (Herr Hs)])
    ltac:(intros Hb;
          apply (ax_blocks_img AX L A (ms_mem ms) md p n (a - ptr_addr L p) HMR Hin ltac:(lia));
          replace (ptr_addr L p + (a - ptr_addr L p)) with a by lia; exact Hi))).
Qed.
End fg.

(** ** Carrying the slot's GI across a free of a block the slot does not keep *)
Section fgi.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma mf_gi_T_pos : forall T m, mf_gi src0_msyms link_mf T m -> forall t, In t T -> 0 < snd t.
Proof.
  intros T m [(_ & ->) | (f & _ & -> & _)] t Ht; [destruct Ht|].
  destruct Ht as [<-|[]]. cbn [snd]. unfold MF_BLOCK. lia.
Qed.

Lemma pw_disj_eq : forall (l : list (Z * Z)) a x y,
  pairwise ranges_disjoint l -> In (a, x) l -> In (a, y) l -> 0 < x -> 0 < y -> x = y.
Proof.
  induction l as [|[b z] l IH]; cbn; intros a x y Hpw Hx Hy Hpx Hpy; [destruct Hx|].
  destruct Hpw as [Hhd Hpw].
  destruct Hx as [Hx|Hx]; destruct Hy as [Hy|Hy].
  - congruence.
  - injection Hx as <- <-. exfalso.
    pose proof (Hhd (b, y) Hy) as Hd. unfold ranges_disjoint in Hd. cbn [fst snd] in Hd. lia.
  - injection Hy as <- <-. exfalso.
    pose proof (Hhd (b, x) Hx) as Hd. unfold ranges_disjoint in Hd. cbn [fst snd] in Hd. lia.
  - exact (IH a x y Hpw Hx Hy Hpx Hpy).
Qed.

Lemma T_block_ne : forall L A p n t T,
  tb_live L A T -> In t T -> ~ In (ptr_addr L p, n) T -> In (p, n) (user_blocks A) ->
  pairwise ranges_disjoint (blocks L A) -> 0 < n -> (forall u, In u T -> 0 < snd u) ->
  exists q sz, In (q, sz) (user_blocks A) /\ q <> p /\ t = (ptr_addr L q, sz).
Proof.
  intros L A p n t T HTL Ht Hnp Hin Hpw Hn Hpos. pose proof HTL as [_ HTL'].
  pose proof (HTL' t Ht) as Hb. unfold blocks in Hb. apply in_map_iff in Hb as ((q & sz) & Hq & Hqin).
  cbn [fst snd] in Hq. exists q, sz. split; [exact Hqin|]. split; [|symmetry; exact Hq].
  intros ->. apply Hnp.
  assert (Hsz : sz = n).
  { apply (pw_disj_eq (blocks L A) (ptr_addr L p) sz n Hpw);
      [ unfold blocks; apply in_map_iff; exists (p, sz); cbn [fst snd]; split; [reflexivity | exact Hqin]
      | unfold blocks; apply in_map_iff; exists (p, n); cbn [fst snd]; split; [reflexivity | exact Hin]
      | pose proof (Hpos t Ht) as Hp0; rewrite <- Hq in Hp0; cbn [snd] in Hp0; exact Hp0
      | exact Hn ]. }
  rewrite <- Hq, Hsz in Ht. exact Ht.
Qed.

Lemma tb_live_after_free : forall L A L' A' p n T,
  tb_live L A T -> ~ In (ptr_addr L p, n) T -> In (p, n) (user_blocks A) ->
  pairwise ranges_disjoint (blocks L A) -> 0 < n -> (forall u, In u T -> 0 < snd u) ->
  (forall q sz, In (q, sz) (user_blocks A) -> q <> p -> In (q, sz) (user_blocks A') /\ ptr_addr L' q = ptr_addr L q) ->
  tb_live L' A' T.
Proof.
  intros L A L' A' p n T HTL Hnp Hin Hpw Hn Hpos Hstab. pose proof HTL as [Hnd' _].
  split; [exact Hnd'|]. intros t Ht.
  destruct (T_block_ne L A p n t T HTL Ht Hnp Hin Hpw Hn Hpos) as (q & sz & Hq & Hqp & ->).
  destruct (Hstab q sz Hq Hqp) as [Hq' Hpa].
  unfold blocks. apply in_map_iff. exists (q, sz). cbn [fst snd]. split; [rewrite Hpa; reflexivity | exact Hq'].
Qed.

Lemma GI_after_free : forall (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop),
  G_local_T src0segs src0_G GI ->
  forall j T L A p n m m',
  GI j T m -> tb_live L A T -> ~ In (ptr_addr L p, n) T -> In (p, n) (user_blocks A) ->
  pairwise ranges_disjoint (blocks L A) -> 0 < n -> (forall u, In u T -> 0 < snd u) ->
  (forall a, in_globals src0_G a -> mbyte src0segs m' a = mbyte src0segs m a) ->
  (forall q sz i, In (q, sz) (user_blocks A) -> q <> p -> 0 <= i < sz ->
     mbyte src0segs m' (ptr_addr L q + i) = mbyte src0segs m (ptr_addr L q + i)) ->
  GI j T m'.
Proof.
  intros GI GIL j T L A p n m m' HGI HTL Hnp Hin Hpw Hn Hpos HG Hbk. apply (GIL j T m m'); [|exact HGI].
  intros a [Ha | (t & k & Ht & Hak)]; [exact (HG a Ha)|].
  destruct (T_block_ne L A p n (t, k) T HTL Ht Hnp Hin Hpw Hn Hpos) as (q & sz & Hq & Hqp & Heq).
  injection Heq as -> ->.
  replace a with (ptr_addr L q + (a - ptr_addr L q)) by lia.
  exact (Hbk q sz (a - ptr_addr L q) Hq Hqp ltac:(lia)).
Qed.
End fgi.

(** The GI conjunct alone, as a slot GI: what the driver carries between the last library call and the exit. *)
Definition mf_GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop :=
  fun _ T m => mf_gi src0_msyms link_mf T m.

Section mfgi.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma mf_GI_local : G_local_T src0segs src0_G mf_GI.
Proof. exact (mf_gi_local src0_msyms link_mf src0_G mf_head_in_G). Qed.

Lemma mf_gi_after_free : forall j T L A L' A' p n m m',
  mf_GI j T m -> tb_live L A T -> ~ In (ptr_addr L p, n) T -> In (p, n) (user_blocks A) ->
  pairwise ranges_disjoint (blocks L A) -> 0 < n ->
  (forall a, in_globals src0_G a -> mbyte src0segs m' a = mbyte src0segs m a) ->
  (forall q sz i, In (q, sz) (user_blocks A) -> q <> p -> 0 <= i < sz ->
     mbyte src0segs m' (ptr_addr L q + i) = mbyte src0segs m (ptr_addr L q + i)) ->
  (forall q sz, In (q, sz) (user_blocks A) -> q <> p -> In (q, sz) (user_blocks A') /\ ptr_addr L' q = ptr_addr L q) ->
  mf_GI j T m' /\ tb_live L' A' T.
Proof.
  intros j T L A L' A' p n m m' HGI HTL Hnp Hin Hpw Hn HG Hbk Hstab.
  pose proof (mf_gi_T_pos T m HGI) as Hpos.
  split.
  - exact (GI_after_free mf_GI mf_GI_local j T L A p n m m' HGI HTL Hnp Hin Hpw Hn Hpos HG Hbk).
  - exact (tb_live_after_free L A L' A' p n T HTL Hnp Hin Hpw Hn Hpos Hstab).
Qed.
End mfgi.

(** ** The statics added back after the split *)
Section stat.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma sx_statics_ok : forall (API : AllocAPI src0_msyms), AllocExtra src0_msyms (aa_MR API) ->
  forall E ss2 ss3 ms L A md,
  st_ok src0segs E ss2 ms -> aa_MR API L A (ms_mem ms) md -> ss_atoms_lt SX_KG ss2 = true ->
  sx_statics ss2 = Some ss3 -> exists E3, st_ok src0segs E3 ss3 ms.
Proof.
  intros API AX E ss2 ss3 ms L A md HS HMR Hat H. unfold sx_statics, drv_add_statics in H.
  destruct (abs_region_index (ss_mem ss2) (ms_got_guard src0_msyms) 0) as [i1|]; [|discriminate].
  destruct (abs_region_index (ss_mem ss2) (ms_libc src0_msyms + 3) 0) as [i2|]; [|discriminate].
  destruct (abs_region_index (ss_mem ss2) (ms_guard src0_msyms) 0) as [i3|]; [|discriminate].
  destruct (add_statics src0_msyms (ss_mem ss2) i1 i2 i3 SX_KG) as [rs|] eqn:Has; [|discriminate].
  injection H as <-.
  destruct (st_ok_statics src0_msyms (aa_MR API) AX E ss2 ms L A md SX_KG i1 i2 i3 rs HS HMR Hat Has)
    as (g & _ & H3).
  exists (ewset E SX_KG (Z_to_bv 64 g)). exact H3.
Qed.
End stat.

(** ** The two transfers the two-arm exit needs, for [realizes] *)
Section rzinst.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable API : AllocAPI src0_msyms.

Lemma rz_run_to : forall (md : Model) (TT : TSet), m_halted md = None -> m_vm_lazy md = [] ->
  forall E0 ss0 ss1 ms0 stop, st_ok src0segs E0 ss0 ms0 ->
  run_to_check src0segs src0tbl stop ss0 = Some ss1 ->
  (forall ms1, st_ok src0segs E0 ss1 ms1 -> frame_of E0 (ss_mem ss0) (ms_mem ms0) (ms_mem ms1) ->
     realizes src0segs (mkCfg ms1 md) TT) ->
  realizes src0segs (mkCfg ms0 md) TT.
Proof.
  intros md TT Hh Hlz E0 ss0 ss1 ms0 stop HS Hr K.
  exact (realizes_run_to src0segs src0tbl src0tbl_ok stop E0 ss0 ss1 ms0 md TT HS Hr Hh Hlz K).
Qed.

Lemma mw_rz : forall (md : Model) (TT : TSet), mwrite_exit_contract_all src0_msyms API ->
  m_halted md = None -> m_vm_lazy md = [] ->
  forall L0 A0 regs mem f, mw_pre src0_msyms API SX_MW_RA L0 A0 regs mem md f ->
  (forall regs' mem', mw_post src0_msyms API L0 A0 regs mem md f regs' mem' ->
     realizes src0segs (mkCfg (mkst regs' (Z_to_bv 64 SX_MW_RA) mem' (seg_rom src0segs)) md) TT) ->
  realizes src0segs (mkCfg (mkst regs (Z_to_bv 64 (mf_write link_mf)) mem (seg_rom src0segs)) md) TT.
Proof.
  intros md TT MWC Hh Hlz L0 A0 regs mem f Hpre K.
  apply (SR_realizes src0segs _ _ TT (MWC fx L0 A0 regs mem md f Hpre)).
  intros c' (regs' & mem' & -> & Hpost). exact (K regs' mem' Hpost).
Qed.
End rzinst.

(** ** The exit sites *)
Section exits.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable API : AllocAPI src0_msyms.
Hypothesis AX : AllocExtra src0_msyms (aa_MR API).
Hypothesis MWC : mwrite_exit_contract_all src0_msyms API.

Theorem src0_exit_mf : forall E ss ms md L A T code,
  st_ok src0segs E ss ms -> stack_anchored E (ss_facts ss) ->
  aa_MR API L A (ms_mem ms) md -> WF A -> bounded A ->
  mf_gi src0_msyms link_mf T (ms_mem ms) -> tb_live L A T ->
  0 <= code < 256 -> exit_mf_check ss code = true ->
  m_halted md = None -> m_vm_lazy md = [] ->
  realizes src0segs (mkCfg ms md) (t_exit (Z_to_bv 64 code) (m_fs md)).
Proof.
  intros E ss ms md L A T code HS HSA HMR HW HB HGI HTL Hcode Hck Hh Hlz.
  unfold exit_mf_check in Hck. destruct (sx_split ss) as [ss2|] eqn:Hsp; [|discriminate].
  apply andb_prop in Hck as [Hatg Hck]. destruct (sx_statics ss2) as [ss3|] eqn:Hst; [|discriminate].
  apply (stdio_exit_two_arm API AX md (fun ms0 => realizes src0segs (mkCfg ms0 md) (t_exit (Z_to_bv 64 code) (m_fs md)))
    (rz_run_to md _ Hh Hlz) (mw_rz API md _ MWC Hh Hlz) E ss ss2 ms L A T HS HSA Hsp HMR HW HB HGI HTL).
  intros E2 ms2 HS2 HMR2.
  destruct (sx_statics_ok API AX E2 ss2 ss3 ms2 L A md HS2 HMR2 Hatg Hst) as (E3 & HS3).
  exact (src0_exit E3 ss3 ms2 md code HS3 Hcode Hck Hh Hlz).
Qed.

Theorem src0_diag_exit_mf : forall E ss ms md ch L A T msg code fd,
  st_ok src0segs E ss ms -> stack_anchored E (ss_facts ss) ->
  aa_MR API L A (ms_mem ms) md -> WF A -> bounded A ->
  mf_gi src0_msyms link_mf T (ms_mem ms) -> tb_live L A T ->
  0 <= code < 256 -> diag_mf_check ss msg code = Some fd ->
  fdchan (Z_to_bv 64 fd) ch md ->
  m_halted md = None -> m_vm_lazy md = [] ->
  realizes src0segs (mkCfg ms md) (t_emit (map (WriteEv ch) msg) (t_exit (Z_to_bv 64 code) (m_fs md))).
Proof.
  intros E ss ms md ch L A T msg code fd HS HSA HMR HW HB HGI HTL Hcode Hck Hch Hh Hlz.
  unfold diag_mf_check in Hck. destruct (sx_split ss) as [ss2|] eqn:Hsp; [|discriminate].
  destruct (ss_atoms_lt SX_KG ss2) eqn:Hatg; [|discriminate].
  destruct (sx_statics ss2) as [ss3|] eqn:Hst; [|discriminate].
  apply (stdio_exit_two_arm API AX md
    (fun ms0 => realizes src0segs (mkCfg ms0 md) (t_emit (map (WriteEv ch) msg) (t_exit (Z_to_bv 64 code) (m_fs md))))
    (rz_run_to md _ Hh Hlz) (mw_rz API md _ MWC Hh Hlz) E ss ss2 ms L A T HS HSA Hsp HMR HW HB HGI HTL).
  intros E2 ms2 HS2 HMR2.
  destruct (sx_statics_ok API AX E2 ss2 ss3 ms2 L A md HS2 HMR2 Hatg Hst) as (E3 & HS3).
  exact (realizes_diag_exit_by_run E3 ss3 ms2 md ch SX_KD msg code fd HS3 Hh Hlz Hcode Hck Hch).
Qed.
End exits.

(** ** The cut-free twins (the [_cfw] driver files)

    The cut-free world (SlotAgree.v [crealizes], [SRcf]) has its own run and site lemmas; the two-arm exit is
    the same theorem, instantiated at [crealizes] with a cut-free mwrite contract. *)
Section cf.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable API : AllocAPI src0_msyms.
Hypothesis AX : AllocExtra src0_msyms (aa_MR API).

Lemma crz_run_to : forall (md : Model) (TT : TSet), m_halted md = None -> m_vm_lazy md = [] ->
  forall E0 ss0 ss1 ms0 stop, st_ok src0segs E0 ss0 ms0 ->
  run_to_check src0segs src0tbl stop ss0 = Some ss1 ->
  (forall ms1, st_ok src0segs E0 ss1 ms1 -> frame_of E0 (ss_mem ss0) (ms_mem ms0) (ms_mem ms1) ->
     crealizes src0_msyms (mkCfg ms1 md) TT) ->
  crealizes src0_msyms (mkCfg ms0 md) TT.
Proof.
  intros md TT Hh Hlz E0 ss0 ss1 ms0 stop HS Hck K. unfold run_to_check in Hck.
  destruct (sym_run_toN src0segs src0tbl FUEL stop ss0) as [ss' st] eqn:Hrun.
  destruct st; try discriminate. destruct (ss_pc ss' =? stop); [|discriminate]. injection Hck as ->.
  exact (crz_run_to_running src0_msyms src0tbl src0tbl_ok FUEL stop E0 ss0 ss1 ms0 md TT Hh Hlz HS Hrun K).
Qed.

Lemma mw_crz : forall (md : Model) (TT : TSet),
  (forall fx' : YK11.FPState, @mwrite_exit_contract_cf fx' rc src0_msyms API SX_MW_RA) ->
  forall L0 A0 regs mem f, mw_pre src0_msyms API SX_MW_RA L0 A0 regs mem md f ->
  (forall regs' mem', mw_post src0_msyms API L0 A0 regs mem md f regs' mem' ->
     crealizes src0_msyms (mkCfg (mkst regs' (Z_to_bv 64 SX_MW_RA) mem' (seg_rom src0segs)) md) TT) ->
  crealizes src0_msyms (mkCfg (mkst regs (Z_to_bv 64 (mf_write link_mf)) mem (seg_rom src0segs)) md) TT.
Proof.
  intros md TT MWC L0 A0 regs mem f Hpre K.
  apply (MWC fx L0 A0 regs mem md f Hpre TT). intros c' (regs' & mem' & -> & Hpost). exact (K regs' mem' Hpost).
Qed.

Hypothesis TBL : forall L A mem md, aa_MR API L A mem md -> forall a, static_owned src0_msyms a -> 0 <= a < 2 ^ 64 ->
  Mem.ro_addr src0segs (Z_to_bv 64 a) = true -> mbyte src0segs mem a = seg_rom src0segs (Z_to_bv 64 a).
Hypothesis FCF : free_contract_cf src0_msyms API.

(** [free_site_cf] (YL0d_cfw.v) with the slot's globals kept, as [free_site_G] is [free_site]. *)
Theorem free_site_cf_G : forall E ss ms md L A p n b sp_off keep blks k l1 rs2 ra T,
  st_ok src0segs E ss ms -> stack_anchored E (ss_facts ss) ->
  site_check src0_msyms ss (ms_free src0_msyms) ra sp_off keep blks k l1 = true ->
  ro_check src0_msyms (ss_mem ss) = true ->
  drv_add_statics src0_msyms (map snd l1) (k + 16) = Some rs2 ->
  aa_MR API L A (ms_mem ms) md -> WF A -> bounded A -> st_init_done A = true ->
  In (p, n) (user_blocks A) ->
  getr (ms_regs ms) 10%bv = Z_to_bv 64 (ptr_addr L p) ->
  res_ok_slots A b ->
  (forall kb sz, In (kb, sz) blks -> exists q, In (q, sz) (user_blocks A) /\ ptr_addr L q = bv_unsigned (ew E kb) /\ q <> p) ->
  (forall A' L' ms' md' g,
     st_ok src0segs (post_env E k (ms_regs ms') g) (post_state ss ra k rs2) ms' ->
     stack_anchored (post_env E k (ms_regs ms') g) (ss_facts ss) ->
     aa_MR API L' A' (ms_mem ms') md' -> WF A' -> bounded A' ->
     (exists vm', md' = with_vmmaps vm' md) ->
     (forall q sz, In (q, sz) (user_blocks A) -> q <> p -> In (q, sz) (user_blocks A') /\ ptr_addr L' q = ptr_addr L q) ->
     (forall a, alloc_ceiling <= a -> a < 2 ^ 64 ->
        ~ (bv_unsigned (ew E 0) + sp_off - ALLOC_STACK <= a < bv_unsigned (ew E 0) + sp_off) ->
        mbyte src0segs (ms_mem ms') a = mbyte src0segs (ms_mem ms) a) ->
     (forall q sz i, In (q, sz) (user_blocks A) -> q <> p -> 0 <= i < sz ->
        mbyte src0segs (ms_mem ms') (ptr_addr L q + i) = mbyte src0segs (ms_mem ms) (ptr_addr L q + i)) ->
     res_ok_slots A' (sb_free b n) ->
     (forall a, in_globals src0_G a -> mbyte src0segs (ms_mem ms') a = mbyte src0segs (ms_mem ms) a) ->
     crealizes src0_msyms (mkCfg ms' md') T) ->
  crealizes src0_msyms (mkCfg ms md) T.
Proof.
  intros E ss ms md L A p n b sp_off keep blks k l1 rs2 ra T HS HSA Hck Hro Hrs2 HMR HW HB Hid Hin Ha0 Hres Hblks HK.
  destruct (site_check_sound src0_msyms _ _ _ _ _ _ _ _ Hck) as (Hpc & Hra & Hrv & Hcp & _).
  pose proof (st_ok_mkst src0segs E ss ms HS Hrv) as Hshape.
  destruct (call_pre_intro src0_msyms (aa_MR API) E ss ms L A md sp_off HS HSA HMR HW HB
    ltac:(intros Hf; rewrite Hid in Hf; discriminate) Hcp) as (Hpre & Hsp & Hsplo).
  assert (Hrag : ro_agree src0segs (ms_mem ms)).
  { apply (ro_agree_of_rodata_ok src0_msyms (ms_mem ms)); [| exact (TBL L A (ms_mem ms) md HMR)].
    destruct HS as (_ & _ & _ & _ & _ & _ & _ & HM & _).
    exact (ro_check_sound src0_msyms E (ms_mem ms) (ss_mem ss) (proj1 (proj2 HM)) Hro). }
  rewrite Hshape in HS |- *. rewrite Hpc in HS |- *. cbn [ms_regs ms_mem mkst] in *.
  apply (FCF L A (ms_regs ms) (ms_mem ms) md p n b Hpre Hrag Hin Ha0 Hres T).
  intros c' (L' & A' & regs' & mem' & md' & -> & Hpost & _ & _ & _ & _ & Hincl & _ & _ & Hres').
  destruct (free_post_cf src0_msyms API AX E ss ms md L A p n sp_off keep blks k l1 rs2 ra regs' mem' md' L' A'
    HS HSA Hck Hrs2 HMR Hin Hsp Hsplo Hblks Hpost Hincl)
    as (g & HS2 & HSA2 & HMR' & HW' & HB' & Hvm & Hkeep & Hhi & Hbk).
  pose proof Hpost as (_ & _ & _ & _ & _ & _ & _ & Himg & _).
  pose proof alloc_ceiling_value as [[Hcmin _] _].
  apply (HK A' L' (mkst regs' (getr (ms_regs ms) 1%bv) mem' (seg_rom src0segs)) md' g
    HS2 HSA2 HMR' HW' HB' Hvm Hkeep Hhi Hbk Hres').
  cbn [ms_mem mkst]. intros a Ha.
  destruct (src0_G_img a Ha) as (Hi & Hst & Hctx & Herr & Hlt).
  assert (Hno : forall L0 A0 m0 d0, aa_MR API L0 A0 m0 d0 -> ~ owned src0_msyms L0 A0 a).
  { intros L0 A0 m0 d0 H0 [Hal|Hso]; [exact (Hctx (ax_img AX L0 A0 m0 d0 a H0 Hi Hal)) | exact (Hst Hso)]. }
  apply (proj1 (Himg a (or_intror Hi) (Hno _ _ _ _ HMR) (Hno _ _ _ _ HMR')
    ltac:(intros [Hs|Hs]; [unfold spZ in Hs; lia | exact (Herr Hs)])
    ltac:(intros Hb;
          apply (ax_blocks_img AX L A (ms_mem ms) md p n (a - ptr_addr L p) HMR Hin ltac:(lia));
          replace (ptr_addr L p + (a - ptr_addr L p)) with a by lia; exact Hi))).
Qed.

Hypothesis MWCF : forall fx' : YK11.FPState, @mwrite_exit_contract_cf fx' rc src0_msyms API SX_MW_RA.

Theorem src0_exit_mf_cf : forall E ss ms md L A T code,
  st_ok src0segs E ss ms -> stack_anchored E (ss_facts ss) ->
  aa_MR API L A (ms_mem ms) md -> WF A -> bounded A ->
  mf_gi src0_msyms link_mf T (ms_mem ms) -> tb_live L A T ->
  0 <= code < 256 -> exit_mf_check ss code = true ->
  m_halted md = None -> m_vm_lazy md = [] ->
  crealizes src0_msyms (mkCfg ms md) (t_exit (Z_to_bv 64 code) (m_fs md)).
Proof.
  intros E ss ms md L A T code HS HSA HMR HW HB HGI HTL Hcode Hck Hh Hlz.
  unfold exit_mf_check in Hck. destruct (sx_split ss) as [ss2|] eqn:Hsp; [|discriminate].
  apply andb_prop in Hck as [Hatg Hck]. destruct (sx_statics ss2) as [ss3|] eqn:Hst; [|discriminate].
  apply (stdio_exit_two_arm API AX md
    (fun ms0 => crealizes src0_msyms (mkCfg ms0 md) (t_exit (Z_to_bv 64 code) (m_fs md)))
    (crz_run_to md _ Hh Hlz) (mw_crz md _ MWCF) E ss ss2 ms L A T HS HSA Hsp HMR HW HB HGI HTL).
  intros E2 ms2 HS2 HMR2.
  destruct (sx_statics_ok API AX E2 ss2 ss3 ms2 L A md HS2 HMR2 Hatg Hst) as (E3 & HS3).
  exact (src0_exit_cf E3 ss3 ms2 md code HS3 Hcode Hck Hh Hlz).
Qed.

Theorem src0_diag_exit_mf_cf : forall E ss ms md ch L A T msg code fd,
  st_ok src0segs E ss ms -> stack_anchored E (ss_facts ss) ->
  aa_MR API L A (ms_mem ms) md -> WF A -> bounded A ->
  mf_gi src0_msyms link_mf T (ms_mem ms) -> tb_live L A T ->
  0 <= code < 256 -> diag_mf_check ss msg code = Some fd ->
  fdchan (Z_to_bv 64 fd) ch md ->
  m_halted md = None -> m_vm_lazy md = [] ->
  crealizes src0_msyms (mkCfg ms md) (t_emit (map (WriteEv ch) msg) (t_exit (Z_to_bv 64 code) (m_fs md))).
Proof.
  intros E ss ms md ch L A T msg code fd HS HSA HMR HW HB HGI HTL Hcode Hck Hch Hh Hlz.
  unfold diag_mf_check in Hck. destruct (sx_split ss) as [ss2|] eqn:Hsp; [|discriminate].
  destruct (ss_atoms_lt SX_KG ss2) eqn:Hatg; [|discriminate].
  destruct (sx_statics ss2) as [ss3|] eqn:Hst; [|discriminate].
  apply (stdio_exit_two_arm API AX md
    (fun ms0 => crealizes src0_msyms (mkCfg ms0 md)
       (t_emit (map (WriteEv ch) msg) (t_exit (Z_to_bv 64 code) (m_fs md))))
    (crz_run_to md _ Hh Hlz) (mw_crz md _ MWCF) E ss ss2 ms L A T HS HSA Hsp HMR HW HB HGI HTL).
  intros E2 ms2 HS2 HMR2.
  destruct (sx_statics_ok API AX E2 ss2 ss3 ms2 L A md HS2 HMR2 Hatg Hst) as (E3 & HS3).
  exact (crealizes_diag_exit_by_run E3 ss3 ms2 md ch SX_KD msg code fd HS3 Hh Hlz Hcode Hck Hch).
Qed.
End cf.

Definition mwrite_exit_contract_cf_all {rc : YM05.RunCeil} (API : AllocAPI src0_msyms) : Prop :=
  forall fx : YK11.FPState, @mwrite_exit_contract_cf fx rc src0_msyms API SX_MW_RA.

(** A slot GI that keeps no block and leaves the three heads at 0 implies the GI conjunct (the G / O form tops,
    whose GI is [fun j T m => T = [] /\ GI j m]). *)
Lemma mf_gi_of_heads0 : forall (GI : nat -> (word -> option byte) -> Prop),
  (forall j m, GI j m -> mf_heads src0_msyms link_mf m 0) ->
  forall j T m, (T = [] /\ GI j m) -> mf_gi src0_msyms link_mf T m.
Proof. intros GI H j T m [-> Hg]. left. split; [exact (H j m Hg) | reflexivity]. Qed.
