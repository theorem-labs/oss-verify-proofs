(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb): the call-site lemmas of rule 1j-bis for the
   texts of lib/A/RPgCSpec.v, at the states those texts already state (the segment contracts' starts and ends, with
   image A's record RPgImgA.role_himg_A). Each lemma shows that the stated state supplies a premise of the next
   call's contract. Proves no function (kind: statement text).
   - role_A_site_malloc_pod: at C2 (0x820c0, role_build_contract's end) a0 = len + (len == 0) = len, and
     8 <= len <= 5440 < MALLOC_MAX: the request premise `0 <= n < MALLOC_MAX` of the allocator's contract
     (lib/Reusable/YG0d.v amalloc_realizes) and the pod size role_check_contract reads.
   - role_A_site_cut3: at C3 (0x820c4, after malloc(pod) returns) the C3 values of role_check_contract's start hold
     when the call kept every register but a0 (which holds pod) and the eight real-frame cells of the C2 list.
   - role_A_site_strs: at role_check_contract's start, the string, cell and table premises of the callee contracts
     M02 calls (rl_check_answer_specX at la = 0x21480, lp = 0x21440, s = 0x21580 / 0x21540; rl_check_code_specX at
     ln = 0x214a0, lm = 0x214c0, sn = 0x21500, sm = 0x21520; rl_refuse_code_specX at tbl = 0x9a680, c0 = 0x21500,
     c1 = 0x21520; rl_parse_specX at akey = 0x215a0 and dcs = the three doubles; the harness's own strcmp at
     0x20ee0) follow from the start state's rl_seg_pre. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK04 YA0n YI04 YP09 YG0v YG00 YG0f YG0n YG0d YCbq YC5d YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Model Layout Spa Role.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec RPgImgA.
Import ListNotations.
Local Open Scope Z_scope.

(* ===================== C2: the malloc(pod) request ===================== *)
Lemma rl_len_bounds : forall rest, 8 <= rl_len rest <= 5440.
Proof.
intros rest. unfold rl_len.
destruct (Model.pod_build rest) as [r rest'] eqn:E. cbn [fst].
pose proof (Spa.buf_header r (Model.pod_build_wf rest r rest' E)) as (_ & _ & _ & H). exact H.
Qed.

Lemma role_A_site_malloc_pod : forall (e : rl_env) (rest : list byte), e_len e = rl_len rest ->
rl_xv e XLenNZ = e_len e /\ 8 <= e_len e <= 5440 /\ 0 <= rl_xv e XLenNZ < MALLOC_MAX.
Proof.
intros e rest He. pose proof (rl_len_bounds rest) as Hb. rewrite <- He in Hb. cbn [rl_xv].
destruct (Z.eqb_spec (e_len e) 0) as [E0|E0]; [lia|].
unfold MALLOC_MAX. lia.
Qed.

(* ===================== C3: the values after malloc(pod) returns ===================== *)
Section c3. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Lemma role_A_site_cut3 : forall H (mem mem' : word -> option byte) (regs regs' : bvmap 5 word) (e : rl_env),
rl_cut segs H mem regs e (hi_L2 role_himg_A) ->
getr regs' (Z_to_bv 5 10) = w64 (e_pod e) ->
(forall r, r <> 10 -> In r [8; 9; 19; 21; 23; 24; 25; 26; 27] -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
(forall o, In o [0x8; 0x28; 0x30; 0x68; 0x78; 0x80] -> forall i, 0 <= i < 8 ->
 mbyte segs (mrestrict H mem') (e_R e + o + i) = mbyte segs (mrestrict H mem) (e_R e + o + i)) ->
rl_cut segs H mem' regs' e (hi_L3 role_himg_A).
Proof.
intros H mem mem' regs regs' e HC H10 Hregs Hcells.
unfold rl_cut in *. cbn [hi_L2 hi_L3 role_himg_A] in *. unfold role_A_L23 in *.
rewrite !Forall_cons_iff in HC.
destruct HC as (_ & C8 & C9 & C19 & C21 & C23 & C24 & C25 & C26 & C27 & R8 & R28 & R30 & R68 & R78 & R80 & _).
cbn [fst snd rl_at rl_xv] in *.
assert (Hc : forall o v, In o [0x8; 0x28; 0x30; 0x68; 0x78; 0x80] ->
  val_mem segs (mrestrict H mem) (e_R e + o) 8 v -> val_mem segs (mrestrict H mem') (e_R e + o) 8 v).
{ intros o v Ho Hv kk Hk. rewrite (Hcells o Ho (Z.of_nat kk)) by lia. exact (Hv kk Hk). }
repeat (apply Forall_cons; [cbn [fst snd rl_at rl_xv] |]); [| | | | | | | | | | | | | | | | apply Forall_nil];
  first
  [ exact H10
  | (rewrite Hregs; [assumption | lia | cbn; tauto])
  | (apply Hc; [cbn; tauto | assumption]) ].
Qed.
End c3.

(* ===================== M02's callees: strings, cells and table at role_check_contract's start ===================== *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Lemma role_A_site_strs : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc mdc RLO RHI e pos,
rl_seg_pre segs B STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc role_himg_A RLO RHI e pos ->
rl_cstr segs (w_H W) memc 0x21480 STR_APPLIED /\ rl_cstr segs (w_H W) memc 0x21440 STR_PENDING /\
rl_cstr segs (w_H W) memc 0x21580 STR_APPLIED /\ rl_cstr segs (w_H W) memc 0x21540 STR_PENDING /\
rl_cstr segs (w_H W) memc 0x214a0 STR_NONE /\ rl_cstr segs (w_H W) memc 0x214c0 STR_MALFORMED /\
rl_cstr segs (w_H W) memc 0x21500 STR_NONE /\ rl_cstr segs (w_H W) memc 0x21520 STR_MALFORMED /\
rl_cstr segs (w_H W) memc 0x215a0 (map (fun x : byte => bv_unsigned x) Role.ROLE_KEY) /\
rl_cstr segs (w_H W) memc 0x20ee0 (map (fun x : byte => bv_unsigned x) Role.ROLE_KEY) /\
rl_ro_cells segs (w_H W) memc [(0x10378, 0x3fe0000000000000); (0x103e0, 0xc1e0000000000000); (0x10330, 0x41e0000000000000)] /\
val_mem segs (mrestrict (w_H W) memc) 0x9a680 8 0x21500 /\ val_mem segs (mrestrict (w_H W) memc) (0x9a680 + 8) 8 0x21520 /\
range_addressable (aview segs (w_H W) memc) SHADOW_OFF 0x9a680 16.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RLO RHI e pos HP.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HG & _ & HS & HC & _).
cbn [hi_globs hi_strs hi_cells role_himg_A] in HG, HS, HC.
rewrite role_A_key_text.
assert (Hs : forall a s, In (a, s) role_A_strs -> rl_cstr segs (w_H W) memc a s)
  by (intros a s Hin; exact (proj1 (Forall_forall _ _) HS (a, s) Hin)).
assert (Hc : forall a v, In (a, v) role_A_cells -> val_mem segs (mrestrict (w_H W) memc) a 8 v)
  by (intros a v Hin; exact (proj1 (Forall_forall _ _) HC (a, v) Hin)).
assert (Hg : forall a n, In (a, n) role_A_globs -> range_addressable (aview segs (w_H W) memc) SHADOW_OFF a n)
  by (intros a n Hin; exact (proj1 (Forall_forall _ _) HG (a, n) Hin)).
unfold STR_APPLIED, STR_PENDING, STR_NONE, STR_MALFORMED.
repeat split;
  first
  [ apply Hs; unfold role_A_strs; cbn [In]; repeat (first [left; reflexivity | right])
  | apply Hc; unfold role_A_cells; cbn [In]; repeat (first [left; reflexivity | right])
  | apply Hg; unfold role_A_globs; cbn [In]; repeat (first [left; reflexivity | right])
  | (unfold rl_ro_cells; repeat constructor; cbn [fst snd]; apply Hc; unfold role_A_cells; cbn [In];
     repeat (first [left; reflexivity | right])) ].
Qed.
End s.

Print Assumptions role_A_site_malloc_pod.
Print Assumptions role_A_site_cut3.
Print Assumptions role_A_site_strs.
