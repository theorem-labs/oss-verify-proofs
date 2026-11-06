(* Image root: the original libreac v1.9.0 set: the pinned fuzz_pcap.asan image
   (sha256 b7a91d9b1fb0017d...) and fuzz_pcap.asan-ubsan (sha256 9e66f771f22af67a...), unstripped twins
   of both; statements of record ed6b6b7b0ab. *)
(* libreac/fuzz_pcap v1.9.0, BOTH ASan images: the deadness of the allocator's environment refusals, stated once, so that
   no walk re-derives it. Every statement is over the SHAPE of the refused request, as cgif_file_fuzzer's
   lib/YG0k.v:11-14 (origin/ossv/recipes c8557374ad2e) writes it: krefusable q = KMapUser | KMapFreeArray | KMmapSec, the
   three kernel requests of the allocator model (Reusable/YG00.v:98-105) whose refused answer leads to PNull (malloc) or
   to a spin (free). No statement names a program counter; the pcs below are comments, measured on both images.

   How cgif makes a refusal dead (the form copied here). A refusal is dead when, at the machine's mmap ecall that answers
   the request, the refused outcome is NOT A STEP of the run's environment: lps's sstep_cfg drops an outcome that is a
   refusal while a non-refusal outcome exists (lps Run.v spurious_refusal_cfg / sstep_cfg_syscall), so with room in the
   budget and a free placement every step is a grant. cgif's allocator walks state this as a node with no spurious
   branch (cgif lib/A/AFkn.v:767-804 node3, MAP_FIXED maps, sp := fun _ => false at :874; lib/A/AFjs.v:513-544 nodeS,
   the secondary map, sp := fun _ => false at :595), fed by placement (AFkn.v PLACE; AFia.v sec_grant_exists_AR) and by
   budget slack (AFkn.v:1203-1210 slack_at, AFjs.v:479-488 slackS, both from YG08.v mroom_slack / rroom_slack). The model
   half is image-free: on a path whose kernel answers are all grants, malloc is not PNull and free does not reach its
   spin (YG0d.v model_laws ml_malloc_ns / ml_free, atok, YG0d.v:185-207 amreal_SRr04).

   The two statement families, and the premise that kills a refusal in each (theories/Shapes.v at ed6b6b7b0ab):
   - agrees (asan_agrees / asan_ubsan_agrees, Statements.v:103-118: agrees_in Env.alloc_forced_only Budgets.Asan.lim_source
     Budgets.Asan.lim_target): the sanitizer run has no budget exemption (Shapes.v:117-127); its limit is
     Budgets.Asan.lim_target = 2^39 (Shapes.v:68-70), cgif's ASAN_VM_LMIN / ASAN_VM_LIMIT (YG0n.v:283-284, YG08.v:156
     vm_budget_slack). Killing premise: the 512 GiB FOOTPRINT, i.e. room eager_used + A_bytes + the request
     <= vm_limit, which mroom (YG0n.v:545, from vm_budget_slack) gives: arefuse_room_agrees below. Form: *_dead_agrees,
     arefuse_node_agrees, over Env.alloc_forced_only (= the core's ACFG, which node_ok and srealizes use).
   - halts (asan_halts / asan_ubsan_halts, Statements.v:78-86: halts_within_budget Budgets.Standard.lim_source
     Exits.ok_or_refused): Env.forced_only, and the premise ~ run_scfg_budget_refused (Shapes.v:282-287). Killing
     premise: at a configuration of such a run, ~ budget_refused_at, whose mmap clause is the negation of lps's own
     budget gate (lps Mmap.v mmap_budget_refused_b). Form: *_dead_halts, over Env.forced_only.
   WHICH FAMILY CITES WHICH IN PCAP'S PORT: both statements come from ONE ASan-side obligation run at the 2^39 limit under
   ACFG (PcapAsanTop.v, cgif_file_fuzzer's AZ03.v / Halts_tfib.v); asan_halts reaches it through Reusable/HaltsKitB.v
   halts_budgets_of_srealizes, whose relim step (must_exit_in_scfg_relim_closed) is the only consumer of the halts budget
   premise. So a walk inside that obligation (srealizes, no cut) cites the *_agrees form for BOTH families; the *_halts
   form is the halts statement's own premise read at one ecall, for a walk run under Env.forced_only at the statement's
   budget (cgif_rgb_fuzzer's lib/HaltsFO.v:72-73 fo_dead form).

   The shapes in fuzz_pcap's two images (MEASURED with python3 + capstone + pyelftools on the unstripped twins; every
   SHF_ALLOC section of each twin equals its pin's except .note.gnu.build-id; asan [asan-ubsan]):
   - mmap itself: internal_mmap 0x64410 [0x64460] = `addi a7,zero,0xde; ecall` (ecall 0x64414 [0x64464]).
   - KMapUser (primary user map, flags 0x32 = MAP_PRIVATE|MAP_ANONYMOUS|MAP_FIXED, prot 3): PopulateFreeArray 0x361a0
     [0x361f0] calls ReservedAddressRange::Map 0x6e360 [0x6e3b0] at 0x362bc [0x3630c] -> MmapFixedOrDieOnFatalError
    0x662a0 [0x662f0] -> MmapFixedImpl 0x66128 [0x66178], internal_mmap call 0x661d0 [0x66220] (flags word 0x32 set by
    the addi at 0x661a0 [0x661f0], stored by the sw that follows it); ENOMEM test 0x66240-0x66244 [0x66290-0x66294]; a zero from Map gives PopulateFreeArray false
     (0x362c0 [0x36310]) and malloc NULL.
   - KMapFreeArray (free array map, same flags; address region_beg + kFreeArrayOffset + mapped, `addi a5,zero,7; slli
     a5,a5,0x1d` 0x33eb0 [0x33f00]): EnsureFreeArraySpace 0x33e64 [0x33eb4] calls Map at 0x33f00 [0x33f50]. Malloc path:
     called from PopulateFreeArray 0x36330 [0x36380], failure -> NULL (0x36334 [0x36384]). FREE path: called from
     ReturnToAllocator 0x33b3c [0x33b8c] at 0x33c9c [0x33cec]; on failure ReturnToAllocator+0x2ec 0x33e28 [0x33e78] calls
     SealedHangOnAllocationFailure 0x33fac [0x33ffc], which SPINS (`j 0` at 0x33fd0 [0x34020]) when
     sealed_report_in_progress is 0: the model's `spin` in ensure_free_array (YG00.v:262-279, spin_on_fail = true from
    return_to_allocator :454-459). Its CHECK new_mapped <= kFreeArrayMax (2^29, loaded by the lui 0x20000 at 0x33ea0) is
    the bgeu at 0x33ea8 [0x33ef8].
   - KMmapSec (secondary map, flags 0x22 = MAP_PRIVATE|MAP_ANONYMOUS, address 0, prot 3): LargeMmapAllocator::Allocate
    0x35920 [0x35970] calls MmapOrDieOnFatalError 0x65cdc [0x65d2c] at 0x359d8 [0x35a28] (flags word 0x22 set by the addi
    at 0x65d30 [0x65d80], stored by the sw that follows it); internal_mmap call 0x65d60 [0x65db0]; ENOMEM test 0x65dc4-0x65dc8 [0x65e14-0x65e18]; a zero is
     NULL (`beqz a0` 0x359dc [0x35a2c]). The split primary/secondary is kMaxSize = 65536 (`lui a5,0x10` 0x356bc [0x3570c]),
     the model's from_primary (YG00.v:72).
   - region ceiling (not an environment refusal, so it has ONE form, used by both families): PopulateFreeArray's test
     mapped_meta + mapped_user + map_size >= 0xE0000001 (`addi a1,zero,7; slli a1,a1,0x1d; addi a1,a1,1; bgeu` 0x36260-
     0x36274 [0x362b0-0x362c4]), i.e. the per-class ceiling kFreeArrayOffset = 3,758,096,384 (YG00.v:15); the model's
     mcheck 222820 (YG00.v:286), dead by atok's areq_ok (YG01.v:14-24): arefuse_ceiling_dead below (malloc) and
     arefuse_ceiling_dead_free (free, whose quarantine batch refill runs the same test).
   - the free path ALLOCATES: QuarantineCache::Enqueue 0x35464 [0x354b4] (called from Quarantine::Put 0x352b4 [0x35304]
     at 0x35454 [0x354a4]) takes a new 8192-byte batch of class 24 (`addi a3,zero,0x18` 0x35594 [0x355e4]) when the
     cache is empty or its batch holds 1021 entries (`addi a7,zero,0x3fd` 0x35494 [0x354e4]), through
     SizeClassAllocator64LocalCache::Refill 0x35d98 [0x35de8], called at 0x355b4 [0x35604], which reaches the KMapUser
     and KMapFreeArray maps above for class 24's region. A failed refill or a null batch goes to 0x355d8 [0x35628],
     which reads the sealed marker (GOT 0x99870 [0x99738]) and sealed_report_in_progress (GOT 0x99878 [0x99740]) and
     SPINS (`j 0` at 0x355f4 [0x35644]); ReportOutOfMemory(8192) at 0x35620 [0x35670] is reached only when the sealed
     marker is 0. The model has this path: enqueue (YG00.v:444-453) calls cache_alloc kBatchClass (= 24, kBatchBytes
     8192, kBatchSlots 1021, YG00.v:26-28) and spins (spin 219184) on None. So no new shape: the node facts are
     arefuse_primary_dead_* and arefuse_freearray_dead_* at class 24, and arefuse_free_spin_refused /
     arefuse_free_realized, stated over the whole free tree, cover this spin as well as return_to_allocator's.
   - fclose (a Theorem Labs lane's reading, not re-checked here): its first free (`ld a0,0xa8(s0)` = f->getln_buf, call 0x8e2b4
     [0x8e180]) is always free(NULL) on pcap, which returns before the allocator; only the second free (the FILE, call
     0x8e2bc [0x8e188]) reaches it.
   In the fd argument both mmaps pass GetNamedMappingFd's answer (0x667bc [0x6680c]), which is -1 when
   decorate_proc_maps is off [INFERENCE: the flag's value in these images is not measured here]; kreq_ecall asks a4 = -1,
   so the walk that reaches the ecall shows it.

   rule 24: no function proved. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
  YK11 YK00 YK02 YK04 YK0i YK0v YK13 YK15 YK18 YP0n YA0i YA0n YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
  YG00 YG0a YG01 YG0k YG0n YG08 YG0b YG0c YF05 YG0d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. The shapes, as the machine issues them.                                                                        *)
(* ---------------------------------------------------------------------------------------------------------------- *)

(* MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, and MAP_PRIVATE | MAP_ANONYMOUS. *)
Definition KMAP_FIXED : Z := 50.
Definition KMAP_ANON : Z := 34.

(* The two primary maps go to a fixed address inside the allocator's reservation; the secondary map is hint-placed. *)
Definition kreq_fixed (q : kreq) : bool :=
  match q with KMapUser _ _ _ | KMapFreeArray _ _ _ => true | _ => false end.
Definition kreq_len (q : kreq) : Z :=
  match q with KMapUser _ _ len | KMapFreeArray _ _ len | KMmapSec len => len | _ => 0 end.
(* base: the primary space's first byte (the core's ly_prim, YG0n.v:315-316). Class c's region starts at region_off c
   (YG00.v:97); its free array at kFreeArrayOffset inside the region (EnsureFreeArraySpace's 7 << 29, see above). *)
Definition kreq_addr (base : Z) (q : kreq) : Z :=
  match q with
  | KMapUser c off _ => base + region_off c + off
  | KMapFreeArray c off _ => base + region_off c + kFreeArrayOffset + off
  | _ => 0
  end.
Definition kreq_flags (q : kreq) : Z := if kreq_fixed q then KMAP_FIXED else KMAP_ANON.
Definition kreq_n (q : kreq) : Z := page_round_up_Z (kreq_len q).

(* The pending ecall is q's mmap: mmap(addr, len, PROT_READ|PROT_WRITE, flags, -1, 0). *)
Definition kreq_ecall (base : Z) (q : kreq) (regs : bvmap 5 word) : Prop :=
  getr regs 17 = Z_to_bv 64 222 /\ getr regs 10 = Z_to_bv 64 (kreq_addr base q) /\
  getr regs 11 = Z_to_bv 64 (kreq_len q) /\ getr regs 12 = Z_to_bv 64 3 /\
  getr regs 13 = Z_to_bv 64 (kreq_flags q) /\ getr regs 14 = Z_to_bv 64 (-1) /\ getr regs 15 = Z_to_bv 64 0.

(* PLACEMENT: a fixed map lies inside the reservation (a mapped, unreserved range: cgif node3's hole = false); the
   secondary map has some free range (anon_node's premise, YF05.v:157). *)
Definition kreq_place (base : Z) (q : kreq) (md : Model) : Prop :=
  if kreq_fixed q then
    0 < kreq_addr base q /\ kreq_addr base q mod page_size = 0 /\
    kreq_addr base q + kreq_n q <= alloc_top (m_vmmaps md) /\
    region_free (vm_reserved (m_vmmaps md)) (Z_to_bv 64 (kreq_addr base q)) (Z_to_bv 64 (kreq_n q)) = true /\
    map_contains (vm_maps (m_vmmaps md)) (Z_to_bv 64 (kreq_addr base q)) (Z_to_bv 64 (kreq_n q)) = true
  else exists a, grant_ok_na_pin md a (kreq_n q) = true.

(* lps's budget gate for this request (the negation of the clause of lps Mmap.v mmap_budget_refused_b it reaches). *)
Definition kreq_budget_ok (base : Z) (q : kreq) (md : Model) : bool :=
  if kreq_fixed q
  then mmap_fixed_rw_budget_ok (Z_to_bv 64 KMAP_FIXED) md (Z_to_bv 64 (kreq_addr base q)) (Z_to_bv 64 (kreq_n q))
  else mmap_noreserve_backed_ok (Z_to_bv 64 KMAP_ANON) md (kreq_n q).

(* A granted answer: the fixed address itself, or a hint-placed address with a free range. Either is below alloc_top,
   so it is never an encoded errno (lps State.v alloc_top_room). *)
Definition kreq_granted (base : Z) (q : kreq) (md : Model) (a : word) : Prop :=
  if kreq_fixed q then a = Z_to_bv 64 (kreq_addr base q) else grant_ok_na_pin md a (kreq_n q) = true.

Definition kreq_grant_md (q : kreq) (md : Model) (a : word) : Model :=
  grant_md (negb (kreq_fixed q)) (Z_to_bv 64 (kreq_flags q)) a (Z_to_bv 64 (kreq_n q)) md.

(* The region-ceiling and free-array-ceiling bounds of a primary map request (areq_ok's, YG01.v:14-24). *)
Definition kceil_ok (s : astate) (q : kreq) : Prop :=
  match q with
  | KMapUser _ off len => off + len <= kFreeArrayOffset
  | KMapFreeArray _ off len => off + len <= kFreeArrayMax
  | _ => True
  end.

(* Every request asked on any path of t satisfies P. *)
Fixpoint aasks {A : Type} (P : astate -> kreq -> Prop) (t : itree astate A) : Prop :=
  match t with
  | IAsk q snap k => P snap q /\ forall z, aok snap q z -> aasks P (k z)
  | _ => True
  end.

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.

Definition kreq_grant_cfg (q : kreq) (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (md : Model)
    (a : word) : config :=
  mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (zfill a (Z_to_bv 64 (kreq_n q)) mem) rom) (kreq_grant_md q md a).

(* THE DEADNESS FACT at one ecall: under cfg, the refused outcome of q is not a step; every step is a grant. *)
Definition kreq_dead (cfg : SpuriousCfg) (base : Z) (q : kreq) (regs : bvmap 5 word) (pc : word)
    (mem rom : word -> option byte) (md : Model) : Prop :=
  forall e st, sstep_cfg segs cfg (mkCfg (pend_at regs pc mem rom) md) e st ->
    e = [] /\ exists a, kreq_granted base q md a /\ st = SNext (kreq_grant_cfg q regs pc mem rom md a).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. The node: with placement and the budget gate, every Env.alloc_forced_only step is the grant.                   *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Lemma kreq_node : forall base q regs pc mem rom md,
  kreq_ecall base q regs -> m_halted md = None -> 0 < kreq_len q < 2 ^ 63 ->
  kreq_place base q md -> kreq_budget_ok base q md = true ->
  exists (I : Type) (nx : I -> config) (i0 : I),
    node_ok segs (mkCfg (pend_at regs pc mem rom) md) I (fun _ => []) nx /\
    forall i, exists a, kreq_granted base q md a /\ nx i = kreq_grant_cfg q regs pc mem rom md a.
Proof.
  intros base q regs pc mem rom md (H17 & H10 & H11 & H12 & H13 & H14 & H15) Hh Hl Hp Hb.
  unfold kreq_place in Hp. unfold kreq_budget_ok in Hb. unfold kreq_flags in H13.
  destruct (kreq_fixed q) eqn:Fq; try rewrite Fq in Hp; try rewrite Fq in Hb; try rewrite Fq in H13.
  - destruct Hp as (HA0 & HAal & HAtop & Hrf & Hmc).
    pose proof (alloc_top_room (m_vmmaps md)) as Hcv. unfold two_pow_64, stack_max_size in Hcv.
    unfold kreq_n in *.
    pose proof (page_round_up_Z_bounds (kreq_len q) ltac:(lia)) as PR. unfold page_size in PR.
    assert (UA : bv_unsigned (Z_to_bv 64 (kreq_addr base q)) = kreq_addr base q) by (apply u64_lit; lia).
    destruct (commit_node3 segs false regs pc mem rom md (Z_to_bv 64 KMAP_FIXED) (Z_to_bv 64 (kreq_addr base q))
      (kreq_len q) Hh H17 H10 ltac:(rewrite UA; exact HAal) ltac:(rewrite UA; exact HA0) H11 ltac:(lia)
      ltac:(rewrite UA; exact HAtop) H12 H13 ltac:(vm_compute; reflexivity) H14 H15 (conj Hrf Hmc) Hb)
      as (I & nx & bit & i0 & Hn & _ & Hx).
    exists I, nx, i0. split; [exact Hn|]. intros i.
    destruct (Hx i) as (md_i & _ & _ & _ & E & Emd).
    exists (Z_to_bv 64 (kreq_addr base q)). split.
    + unfold kreq_granted. rewrite Fq. reflexivity.
    + rewrite E, Emd. unfold kreq_grant_cfg, kreq_grant_md, kreq_flags, kreq_n. rewrite Fq. reflexivity.
  - assert (HA : kreq_addr base q = 0) by (destruct q; try discriminate Fq; reflexivity).
    rewrite HA in H10. unfold kreq_n in *.
    destruct (anon_node segs regs pc mem rom md (Z_to_bv 64 KMAP_ANON) (kreq_len q) Hh H17 H10 H11 ltac:(lia)
      H12 H13 ltac:(vm_compute; reflexivity) H14 H15 Hp Hb) as (I & nx & bit & ga & i0 & Hn & _ & Hx).
    exists I, nx, i0. split; [exact Hn|]. intros i.
    destruct (Hx i) as (md_i & _ & _ & _ & Hg & E & Emd).
    exists (ga i). split.
    + unfold kreq_granted. rewrite Fq. exact Hg.
    + rewrite E, Emd. unfold kreq_grant_cfg, kreq_grant_md, kreq_flags, kreq_n, grant_md. rewrite Fq. reflexivity.
Qed.

Lemma kreq_dead_of_node : forall cfg base q regs pc mem rom md (I : Type) (nx : I -> config),
  cfg_le cfg Env.alloc_forced_only ->
  node_ok segs (mkCfg (pend_at regs pc mem rom) md) I (fun _ => []) nx ->
  (forall i, exists a, kreq_granted base q md a /\ nx i = kreq_grant_cfg q regs pc mem rom md a) ->
  kreq_dead cfg base q regs pc mem rom md.
Proof.
  intros cfg base q regs pc mem rom md I nx Hle [_ Hc] Hnx e st Hs.
  pose proof (sstep_cfg_mono segs cfg Env.alloc_forced_only _ _ _ Hle Hs) as Hs'.
  destruct (Hc e st Hs') as (i & -> & ->). split; [reflexivity|].
  destruct (Hnx i) as (a & Ha & E). exists a. split; [exact Ha | rewrite E; reflexivity].
Qed.

(* The halts statement's budget premise, read at one ecall: not budget-refused here means the gate passes. *)
Lemma kreq_budget_of_not_refused : forall base q regs pc mem rom md,
  kreq_ecall base q regs -> m_halted md = None -> 0 < kreq_len q < 2 ^ 63 -> kreq_place base q md ->
  ~ budget_refused_at segs (mkCfg (pend_at regs pc mem rom) md) -> kreq_budget_ok base q md = true.
Proof.
  intros base q regs pc mem rom md (H17 & H10 & H11 & H12 & H13 & H14 & H15) Hh Hl Hp Hnr.
  destruct (kreq_budget_ok base q md) eqn:Eb; [reflexivity|]. exfalso. apply Hnr.
  assert (Hno : bv_unsigned (getr regs 17) = 222) by (rewrite H17; reflexivity).
  assert (Hlen0 : getr regs 11 <> Z_to_bv 64 0).
  { rewrite H11. intros E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E.
    change (bv_wrap 64 0) with 0 in E.
    rewrite bv_wrap_small in E; [lia | change (bv_modulus 64) with (2 ^ 64); lia]. }
  assert (Hw : w_is0 (getr regs 11) = false) by (unfold w_is0; apply bv_eqb_neq; exact Hlen0).
  assert (Hru : page_round_up_Z (bv_unsigned (getr regs 11)) = kreq_n q).
  { rewrite H11, Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). reflexivity. }
  pose proof (alloc_top_room (m_vmmaps md)) as Hcv. unfold two_pow_64, stack_max_size in Hcv.
  assert (PR : kreq_len q <= kreq_n q)
    by (unfold kreq_n; pose proof (page_round_up_Z_bounds (kreq_len q) ltac:(lia)); lia).
  split; [exact Hh|]. right. exists (getr regs 17). split; [reflexivity|]. left.
  cbn [cfg_ms cfg_model]. unfold alloc_budget_refused_b. cbv zeta.
  rewrite si_sysno, Hno, si_arg0, si_arg1, si_arg2, si_arg3, si_arg4, si_arg5, H10, H12, H13, H14, H15.
  unfold Mmap.mmap_budget_refused_b. cbv zeta. rewrite Hw, Hru.
  unfold kreq_place in Hp. unfold kreq_budget_ok in Eb.
  destruct (kreq_fixed q) eqn:Fq; try rewrite Fq in Hp; try rewrite Fq in Eb.
  - destruct Hp as (HA0 & HAal & HAtop & Hrf & Hmc).
    assert (Eb' : mmap_fixed_rw_budget_ok (Z_to_bv 64 KMAP_FIXED) md (Z_to_bv 64 (kreq_addr base q))
      (Z_to_bv 64 (kreq_n q)) = false) by exact Eb.
    replace (kreq_flags q) with KMAP_FIXED by (unfold kreq_flags; rewrite Fq; reflexivity).
    rewrite (u64_lit (kreq_addr base q)) by lia.
    replace (two_pow_64 <=? kreq_addr base q + kreq_n q) with false
      by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia).
    replace (kreq_addr base q + kreq_n q <=? alloc_top (m_vmmaps md)) with true
      by (symmetry; apply Z.leb_le; exact HAtop).
    replace (kreq_addr base q mod page_size =? 0) with true by (symmetry; apply Z.eqb_eq; exact HAal).
    replace (0 <? kreq_addr base q) with true by (symmetry; apply Z.ltb_lt; exact HA0).
    rewrite Hrf, Hmc, Eb'. reflexivity.
  - assert (Eb' : mmap_noreserve_backed_ok (Z_to_bv 64 KMAP_ANON) md (kreq_n q) = false) by exact Eb.
    replace (kreq_flags q) with KMAP_ANON by (unfold kreq_flags; rewrite Fq; reflexivity).
    rewrite Eb'. reflexivity.
Qed.

(* The footprint premise: with room, the budget gate passes, and the grant keeps the world invariant (commit_AI). *)
Lemma kreq_commit : forall base q (Hh : word -> bool) (A : list (Z * Z)) md,
  0 < kreq_len q < 2 ^ 63 -> kreq_place base q md ->
  AI segs Hh A md -> MWF md -> eager_used md + A_bytes A + kreq_n q <= vm_limit (m_vmmaps md) ->
  kreq_budget_ok base q md = true /\
  forall a, kreq_granted base q md a -> AI segs Hh A (kreq_grant_md q md a) /\ MWF (kreq_grant_md q md a).
Proof.
  intros base q Hh A md Hl Hp HAI HW Hs.
  pose proof (alloc_top_room (m_vmmaps md)) as Hcv. unfold two_pow_64, stack_max_size in Hcv.
  unfold kreq_place in Hp. unfold kreq_budget_ok, kreq_granted, kreq_grant_md, kreq_n, kreq_flags.
  unfold kreq_n in Hs, Hp.
  destruct (kreq_fixed q) eqn:Fq; try rewrite Fq in Hp; cbn [negb].
  - destruct Hp as (HA0 & HAal & HAtop & Hrf & Hmc).
    pose proof (page_round_up_Z_bounds (kreq_len q) ltac:(lia)) as PR. unfold page_size in PR.
    assert (UA : bv_unsigned (Z_to_bv 64 (kreq_addr base q)) = kreq_addr base q) by (apply u64_lit; lia).
    destruct (commit_AI segs Hh A md false (Z_to_bv 64 KMAP_FIXED) (Z_to_bv 64 (kreq_addr base q)) (kreq_len q)
      HAI HW ltac:(vm_compute; reflexivity) ltac:(rewrite UA; exact HAal) ltac:(lia) ltac:(rewrite UA; exact HAtop)
      (conj Hrf Hmc) Hs) as [[HAI' HW'] Hb].
    split; [exact Hb|]. intros a ->. split; [exact HAI' | exact HW'].
  - destruct Hp as (a0 & Ha0).
    assert (C : forall a, grant_ok_na_pin md a (page_round_up_Z (kreq_len q)) = true ->
      (AI segs Hh A (grant_md true (Z_to_bv 64 KMAP_ANON) a (Z_to_bv 64 (page_round_up_Z (kreq_len q))) md) /\
       MWF (grant_md true (Z_to_bv 64 KMAP_ANON) a (Z_to_bv 64 (page_round_up_Z (kreq_len q))) md)) /\
      mmap_noreserve_backed_ok (Z_to_bv 64 KMAP_ANON) md (page_round_up_Z (kreq_len q)) = true).
    { intros a Ha. unfold grant_ok_na_pin in Ha.
      apply andb_prop in Ha as [Ha Hrf]. apply andb_prop in Ha as [Ha Hce]. apply andb_prop in Ha as [Hal _].
      apply Z.eqb_eq in Hal. apply Z.leb_le in Hce.
      exact (commit_AI segs Hh A md true (Z_to_bv 64 KMAP_ANON) a (kreq_len q) HAI HW ltac:(vm_compute; reflexivity)
        Hal ltac:(lia) Hce Hrf Hs). }
    split; [exact (proj2 (C a0 Ha0))|]. intros a Ha. exact (proj1 (C a Ha)).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. The deadness facts, both forms, generic over the krefusable shape.                                             *)
(* ---------------------------------------------------------------------------------------------------------------- *)

(* HALTS form: the halts statement's budget premise (Shapes.v:282-287) at this configuration kills the refusal under
   Env.forced_only. *)
Theorem arefuse_dead_halts : forall base q regs pc mem rom md,
  krefusable q = true -> kreq_ecall base q regs -> m_halted md = None -> 0 < kreq_len q < 2 ^ 63 ->
  kreq_place base q md -> ~ budget_refused_at segs (mkCfg (pend_at regs pc mem rom) md) ->
  kreq_dead Env.forced_only base q regs pc mem rom md.
Proof.
  intros base q regs pc mem rom md _ He Hh Hl Hp Hnr.
  destruct (kreq_node base q regs pc mem rom md He Hh Hl Hp
    (kreq_budget_of_not_refused base q regs pc mem rom md He Hh Hl Hp Hnr)) as (I & nx & i0 & Hn & Hx).
  exact (kreq_dead_of_node Env.forced_only base q regs pc mem rom md I nx (forced_only_cfg_least _) Hn Hx).
Qed.

(* AGREES form: the 512 GiB footprint (room under vm_limit) kills the refusal under Env.alloc_forced_only, and the
   grant keeps AI / MWF. *)
Theorem arefuse_dead_agrees : forall base q regs pc mem rom md (Hh : word -> bool) (A : list (Z * Z)),
  krefusable q = true -> kreq_ecall base q regs -> 0 < kreq_len q < 2 ^ 63 -> kreq_place base q md ->
  AI segs Hh A md -> MWF md -> eager_used md + A_bytes A + kreq_n q <= vm_limit (m_vmmaps md) ->
  kreq_dead Env.alloc_forced_only base q regs pc mem rom md /\
  (forall a, kreq_granted base q md a -> AI segs Hh A (kreq_grant_md q md a) /\ MWF (kreq_grant_md q md a)).
Proof.
  intros base q regs pc mem rom md Hh A _ He Hl Hp HAI HW Hs.
  destruct (kreq_commit base q Hh A md Hl Hp HAI HW Hs) as [Hb HG].
  destruct (kreq_node base q regs pc mem rom md He (AI_halted segs Hh A md HAI) Hl Hp Hb) as (I & nx & i0 & Hn & Hx).
  split; [|exact HG].
  exact (kreq_dead_of_node Env.alloc_forced_only base q regs pc mem rom md I nx (cfg_le_refl _) Hn Hx).
Qed.

(* The AGREES form as cgif's allocator walks use it: the IAsk obligation of amreal (YG0d.v amreal) at the ecall, with no
   spurious branch (cgif lib/A/AFkn.v:767-804 node3, lib/A/AFjs.v:513-544 nodeS). *)
Theorem arefuse_node_agrees {R : Type} : forall (W : world segs) base q snap (k : Z -> itree astate R)
    (Q : R -> world segs -> config -> Prop) regs pc mem rom md,
  krefusable q = true -> kreq_ecall base q regs -> 0 < kreq_len q < 2 ^ 63 -> kreq_place base q md ->
  AI segs (w_H W) (w_A W) md -> MWF md -> eager_used md + A_bytes (w_A W) + kreq_n q <= vm_limit (m_vmmaps md) ->
  (forall a, kreq_granted base q md a -> amreal segs (k 1) W (kreq_grant_cfg q regs pc mem rom md a) Q) ->
  exists (I : Type) (nx : I -> config) (bit : I -> Z) (sp : I -> bool) (i0 : I),
    node_ok segs (mkCfg (pend_at regs pc mem rom) md) I (fun _ => []) nx /\
    (forall i, AI segs (w_H W) (w_A W) md -> AI segs (w_H W) (w_A W) (cfg_model (nx i))) /\
    (forall i, aok snap q (bit i)) /\ sp i0 = false /\ bit i0 = 1 /\
    (forall i, sp i = false -> bit i = 1) /\
    (forall i, sp i = true -> AI segs (w_H W) (w_A W) (cfg_model (nx i)) -> srealizes segs (nx i) t_nil) /\
    (forall i, sp i = false -> amreal segs (k (bit i)) W (nx i) Q).
Proof.
  intros W base q snap k Q regs pc mem rom md Hq He Hl Hp HAI HW Hs Hk.
  destruct (kreq_commit base q (w_H W) (w_A W) md Hl Hp HAI HW Hs) as [Hb HG].
  destruct (kreq_node base q regs pc mem rom md He (AI_halted segs _ _ md HAI) Hl Hp Hb) as (I & nx & i0 & Hn & Hx).
  exists I, nx, (fun _ => 1), (fun _ => false), i0.
  split; [exact Hn|].
  split; [intros i _; destruct (Hx i) as (a & Ha & ->); exact (proj1 (HG a Ha))|].
  split; [intros i; destruct q; try discriminate Hq; cbn; right; reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [intros i _; reflexivity|].
  split; [intros i E; discriminate E|].
  intros i _. destruct (Hx i) as (a & Ha & ->). exact (Hk a Ha).
Qed.

(* The agrees form's room, from the footprint: mroom (ameter + VM_HEAD <= ASAN_VM_LMIN, YG0n.v:545; vm_budget_slack
   YG08.v:156) through mroom_slack (YG08.v:179). *)
Lemma arefuse_room_agrees : forall U ly s md0 md (a0 a k n : Z),
  Wf U s -> ALedger segs ly s md0 -> a0 <= abudget s -> mroom s ->
  vm_limit (m_vmmaps md) = vm_limit (m_vmmaps md0) -> eager_used md <= eager_used md0 + k -> a <= a0 + k -> 0 <= k ->
  n + 2 * k <= VM_HEAD ->
  eager_used md + a + n <= vm_limit (m_vmmaps md).
Proof.
  intros U ly s md0 md a0 a k n W L HA HM LIM EG AB Hk Hn.
  pose proof (mroom_slack segs U ly s md0 md a0 a k W L HA HM LIM EG AB Hk) as MS. lia.
Qed.

(* The footprint's limit is the agrees statements' sanitizer budget. *)
Lemma arefuse_limit_is_lim_target : ASAN_VM_LMIN = Budgets.Asan.lim_target.
Proof. rewrite (proj2 asan_budgets). reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. Per shape (the names the walks cite).                                                                          *)
(* ---------------------------------------------------------------------------------------------------------------- *)

(* KMapUser: the primary user map (PopulateFreeArray -> ReservedAddressRange::Map -> MmapFixedImpl). *)
Theorem arefuse_primary_dead_halts : forall base c off len regs pc mem rom md,
  kreq_ecall base (KMapUser c off len) regs -> m_halted md = None -> 0 < len < 2 ^ 63 ->
  kreq_place base (KMapUser c off len) md -> ~ budget_refused_at segs (mkCfg (pend_at regs pc mem rom) md) ->
  kreq_dead Env.forced_only base (KMapUser c off len) regs pc mem rom md.
Proof.
  intros base c off len regs pc mem rom md He Hh Hl Hp Hnr.
  exact (arefuse_dead_halts base (KMapUser c off len) regs pc mem rom md eq_refl He Hh Hl Hp Hnr).
Qed.
Theorem arefuse_primary_dead_agrees : forall base c off len regs pc mem rom md (Hh : word -> bool) (A : list (Z * Z)),
  kreq_ecall base (KMapUser c off len) regs -> 0 < len < 2 ^ 63 -> kreq_place base (KMapUser c off len) md ->
  AI segs Hh A md -> MWF md -> eager_used md + A_bytes A + page_round_up_Z len <= vm_limit (m_vmmaps md) ->
  kreq_dead Env.alloc_forced_only base (KMapUser c off len) regs pc mem rom md /\
  (forall a, kreq_granted base (KMapUser c off len) md a ->
     AI segs Hh A (kreq_grant_md (KMapUser c off len) md a) /\ MWF (kreq_grant_md (KMapUser c off len) md a)).
Proof.
  intros base c off len regs pc mem rom md Hh A He Hl Hp HAI HW Hs.
  exact (arefuse_dead_agrees base (KMapUser c off len) regs pc mem rom md Hh A eq_refl He Hl Hp HAI HW Hs).
Qed.

(* KMapFreeArray: the free array map (EnsureFreeArraySpace -> Map). On the free path its refusal is the SPIN of
   SealedHangOnAllocationFailure; on the malloc path it is a NULL. *)
Theorem arefuse_freearray_dead_halts : forall base c off len regs pc mem rom md,
  kreq_ecall base (KMapFreeArray c off len) regs -> m_halted md = None -> 0 < len < 2 ^ 63 ->
  kreq_place base (KMapFreeArray c off len) md -> ~ budget_refused_at segs (mkCfg (pend_at regs pc mem rom) md) ->
  kreq_dead Env.forced_only base (KMapFreeArray c off len) regs pc mem rom md.
Proof.
  intros base c off len regs pc mem rom md He Hh Hl Hp Hnr.
  exact (arefuse_dead_halts base (KMapFreeArray c off len) regs pc mem rom md eq_refl He Hh Hl Hp Hnr).
Qed.
Theorem arefuse_freearray_dead_agrees : forall base c off len regs pc mem rom md (Hh : word -> bool) (A : list (Z * Z)),
  kreq_ecall base (KMapFreeArray c off len) regs -> 0 < len < 2 ^ 63 -> kreq_place base (KMapFreeArray c off len) md ->
  AI segs Hh A md -> MWF md -> eager_used md + A_bytes A + page_round_up_Z len <= vm_limit (m_vmmaps md) ->
  kreq_dead Env.alloc_forced_only base (KMapFreeArray c off len) regs pc mem rom md /\
  (forall a, kreq_granted base (KMapFreeArray c off len) md a ->
     AI segs Hh A (kreq_grant_md (KMapFreeArray c off len) md a) /\
     MWF (kreq_grant_md (KMapFreeArray c off len) md a)).
Proof.
  intros base c off len regs pc mem rom md Hh A He Hl Hp HAI HW Hs.
  exact (arefuse_dead_agrees base (KMapFreeArray c off len) regs pc mem rom md Hh A eq_refl He Hl Hp HAI HW Hs).
Qed.

(* KMmapSec: the secondary map (LargeMmapAllocator::Allocate -> MmapOrDieOnFatalError). *)
Theorem arefuse_secondary_dead_halts : forall base len regs pc mem rom md,
  kreq_ecall base (KMmapSec len) regs -> m_halted md = None -> 0 < len < 2 ^ 63 ->
  kreq_place base (KMmapSec len) md -> ~ budget_refused_at segs (mkCfg (pend_at regs pc mem rom) md) ->
  kreq_dead Env.forced_only base (KMmapSec len) regs pc mem rom md.
Proof.
  intros base len regs pc mem rom md He Hh Hl Hp Hnr.
  exact (arefuse_dead_halts base (KMmapSec len) regs pc mem rom md eq_refl He Hh Hl Hp Hnr).
Qed.
Theorem arefuse_secondary_dead_agrees : forall base len regs pc mem rom md (Hh : word -> bool) (A : list (Z * Z)),
  kreq_ecall base (KMmapSec len) regs -> 0 < len < 2 ^ 63 -> kreq_place base (KMmapSec len) md ->
  AI segs Hh A md -> MWF md -> eager_used md + A_bytes A + page_round_up_Z len <= vm_limit (m_vmmaps md) ->
  kreq_dead Env.alloc_forced_only base (KMmapSec len) regs pc mem rom md /\
  (forall a, kreq_granted base (KMmapSec len) md a ->
     AI segs Hh A (kreq_grant_md (KMmapSec len) md a) /\ MWF (kreq_grant_md (KMmapSec len) md a)).
Proof.
  intros base len regs pc mem rom md Hh A He Hl Hp HAI HW Hs.
  exact (arefuse_dead_agrees base (KMmapSec len) regs pc mem rom md Hh A eq_refl He Hl Hp HAI HW Hs).
Qed.

End r.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 5. The model half (image-free, both families): only a refused answer reaches PNull or the spin; the ceilings hold. *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Lemma atok_aasks {A : Type} : forall (t : itree astate A) ns Q, atok ns t Q -> aasks areq_ok t.
Proof.
  induction t as [a | q snap k IH | pc | f]; cbn; intros ns Q H; auto.
  destruct H as [Hr Hk]. split; [exact Hr|]. intros z Hz. exact (IH z _ Q (Hk z Hz)).
Qed.

Lemma aasks_mono {A : Type} : forall (P P' : astate -> kreq -> Prop) (t : itree astate A),
  (forall s q, P s q -> P' s q) -> aasks P t -> aasks P' t.
Proof.
  intros P P' t HP. induction t as [a | q snap k IH | pc | f]; cbn; auto.
  intros [Hq Hk]. split; [exact (HP _ _ Hq)|]. intros z Hz. exact (IH z (Hk z Hz)).
Qed.

Lemma atok_aspins_flag {A : Type} : forall (t : itree astate A) ns Q tr pc,
  atok ns t Q -> aspins t tr pc -> last_flag ns tr = false.
Proof.
  induction t as [a | q snap k IH | pc' | f]; cbn; intros ns Q tr pc H Hy.
  - destruct tr; destruct Hy.
  - destruct tr as [|[q' z] tr']; [destruct Hy|]. destruct Hy as (-> & Hz & Hy). destruct H as [_ Hk].
    exact (IH z _ Q tr' pc (Hk z Hz) Hy).
  - destruct tr; [exact H | destruct Hy].
  - destruct H.
Qed.

(* KMapUser / KMapFreeArray / KMmapSec on the malloc path: malloc's checks never fail (asafe), and a NULL result needs a
   refused answer on its path (gflag = false). *)
Theorem arefuse_malloc_null_refused : forall U s n trc,
  model_laws U -> Wf U s -> st_nev s < EV_MAX -> 0 <= n < MALLOC_MAX -> blocks_bytes s + n <= LIVE_MAX -> In trc U ->
  asafe (malloc n trc s) /\ forall tr r, apath (malloc n trc s) tr r -> fst r = PNull -> gflag tr = false.
Proof.
  intros U s n trc ML W Hev Hn Hl Ht.
  pose proof (ml_malloc_ns U ML s n trc W (or_introl Hev) Hn Hl Ht) as T.
  split; [exact (atok_asafe _ _ _ T)|].
  intros tr r Hp Hnull. destruct (gflag tr) eqn:G; [|reflexivity].
  pose proof (atok_apath_flag _ _ _ tr r T Hp) as [_ HN]. rewrite (last_flag_true tr G) in HN.
  discriminate (HN Hnull).
Qed.

(* KMapFreeArray on the free path: free's checks never fail, and its spin needs a refused answer on its path. *)
Theorem arefuse_free_spin_refused : forall U s p n trc,
  model_laws U -> Wf U s -> st_nev s < EV_MAX -> (p = PNull \/ In (p, n) (blocks s)) -> In trc U ->
  asafe (free p trc s) /\ forall tr pc, aspins (free p trc s) tr pc -> gflag tr = false.
Proof.
  intros U s p n trc ML W Hev Hp Ht.
  pose proof (ml_free U ML s p n trc W Hev Hp Ht) as T.
  split; [exact (atok_asafe _ _ _ T)|].
  intros tr pc Hy. destruct (gflag tr) eqn:G; [|reflexivity].
  pose proof (atok_aspins_flag _ _ _ tr pc T Hy) as F. rewrite (last_flag_true tr G) in F. discriminate F.
Qed.

(* The region ceiling (and the free array's): every primary map malloc asks stays at or below kFreeArrayOffset (the
   region) / kFreeArrayMax (the free array). One form: no environment refusal is involved. *)
Theorem arefuse_ceiling_dead : forall U s n trc,
  model_laws U -> Wf U s -> st_nev s < EV_MAX -> 0 <= n < MALLOC_MAX -> blocks_bytes s + n <= LIVE_MAX -> In trc U ->
  aasks kceil_ok (malloc n trc s).
Proof.
  intros U s n trc ML W Hev Hn Hl Ht.
  apply (aasks_mono areq_ok).
  - intros s' q Hq. destruct q; cbn [kceil_ok]; try exact I; unfold areq_ok in Hq;
      destruct Hq as (_ & _ & _ & _ & _ & H & _); exact H.
  - exact (atok_aasks _ _ _ (ml_malloc_ns U ML s n trc W (or_introl Hev) Hn Hl Ht)).
Qed.

(* The same ceilings on the free path: the quarantine batch refill (enqueue's cache_alloc kBatchClass) and the
   free-array map of return_to_allocator ask only requests within them. *)
Theorem arefuse_ceiling_dead_free : forall U s p n trc,
  model_laws U -> Wf U s -> st_nev s < EV_MAX -> (p = PNull \/ In (p, n) (blocks s)) -> In trc U ->
  aasks kceil_ok (free p trc s).
Proof.
  intros U s p n trc ML W Hev Hp Ht.
  apply (aasks_mono areq_ok).
  - intros s' q Hq. destruct q; cbn [kceil_ok]; try exact I; unfold areq_ok in Hq;
      destruct Hq as (_ & _ & _ & _ & _ & H & _); exact H.
  - exact (atok_aasks _ _ _ (ml_free U ML s p n trc W Hev Hp Ht)).
Qed.

Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.

(* A walk holding amreal for malloc (the core's amalloc_realizes, YG0d.v:254-261) reaches only granted paths, and on
   them malloc is not NULL: the refusals of all three shapes are dead. *)
Theorem arefuse_malloc_realized : forall (W : world segs) c (Q : sptr * astate -> world segs -> config -> Prop) U s n trc,
  model_laws U -> Wf U s -> st_nev s < EV_MAX -> 0 <= n < MALLOC_MAX -> blocks_bytes s + n <= LIVE_MAX -> In trc U ->
  amreal segs (malloc n trc s) W c Q ->
  SRr segs W c (fun W' c' => exists r tr, apath (malloc n trc s) tr r /\ gflag tr = true /\ fst r <> PNull /\ Q r W' c').
Proof.
  intros W c Q U s n trc ML Wf0 Hev Hn Hl Ht H.
  pose proof (ml_malloc_ns U ML s n trc Wf0 (or_introl Hev) Hn Hl Ht) as T.
  eapply SRr_mono.
  { exact (amreal_SRr04 segs _ W c Q H (atok_asafe _ _ _ T) (atok_agprog _ _ _ T) (atok_nospin _ _ T)). }
  intros W' c' _ (r & tr & Hp & G & HQ). exists r, tr. split; [exact Hp|]. split; [exact G|]. split; [|exact HQ].
  intros Hnull. pose proof (atok_apath_flag _ _ _ tr r T Hp) as [_ HN]. rewrite (last_flag_true tr G) in HN.
  discriminate (HN Hnull).
Qed.

(* A walk holding amreal for free (the core's afree_realizes, YG0d.v:270-277) reaches only returns on granted paths: the
   free-array map's refusal, and with it the spin, is dead. *)
Theorem arefuse_free_realized : forall (W : world segs) c (Q : unit * astate -> world segs -> config -> Prop) U s p n trc,
  model_laws U -> Wf U s -> st_nev s < EV_MAX -> (p = PNull \/ In (p, n) (blocks s)) -> In trc U ->
  amreal segs (free p trc s) W c Q ->
  SRr segs W c (fun W' c' => exists r tr, apath (free p trc s) tr r /\ gflag tr = true /\ Q r W' c').
Proof.
  intros W c Q U s p n trc ML Wf0 Hev Hp Ht H.
  pose proof (ml_free U ML s p n trc Wf0 Hev Hp Ht) as T.
  exact (amreal_SRr04 segs _ W c Q H (atok_asafe _ _ _ T) (atok_agprog _ _ _ T) (atok_nospin _ _ T)).
Qed.

End m.
