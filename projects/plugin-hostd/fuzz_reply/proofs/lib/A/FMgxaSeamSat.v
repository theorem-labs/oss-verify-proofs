(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMgxaSeamSat.v (a working branch 3242941dc96); relocated to plugin-hostd/fuzz_reply/fuzz_reply.asan by a Theorem Labs lane's pfinst/tool (reloc.py target reply-A): module paths changed; 25 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_reply.asan, symbol + offset; table pfinst/tool/tables-3242941dc96/reply-A/FMgxaSeamSat.table); by hand (numerals.py BY_HAND, reason in the table): 0x929a8 -> 0x96900, 0x92f68 -> 0x96e48; names: record RT_IImgA -> . *)
(* SATISFIABILITY CONTROL for the GXA seam's READY (FMgxaSeam.v:317-328): seam_calls_ready (FMgxaSeamGuard.v:100) at
   fm's three readiness predicates FMgxa_mem.copy_ready, FMgxa_mem.set_ready and RT_gxa_strnlen.strn_ready holds at a
   store and a geometry where every clause has calls to cover.

   A witness where the clauses hold vacuously proves nothing: with lo + OUT_DEPTH > q - 368 no sp meets a clause's
   stack premises.  seam_ready_sat states the geometry that rules this out (memcpy, memset and strnlen calls all exist
   below q - 368, the window is the seam's VFA_DEPTH, the FILE and the cookie sit above it, the destination is
   non-empty, all in high memory below 2^47), and seam_ready_sat_calls instantiates each clause at one concrete call.

   The geometry is fm's snprintf call chain at fm.asan, with S the snprintf caller's sp:
     S   = 0x7fffffffe000        a concrete high stack address: page-aligned, 8 KiB below 2^47 and above the highest
                                 alloc_ceiling 0x7fffff800000 (YG0f.v:16 ASAN_CEIL_range)
     q   = sp0 = S - 0xa30       musl vfprintf's entry sp (a Theorem Labs lane's design/SNPRINTF-SHARED.md, stack windows table;
                                 FMsnprintfGI.v:14-15: the snprintf interceptor is entered at sp0 + 0xa30)
     lo  = q - 5552              the seam's window VFA_DEPTH = 368 + PC_DEPTH (G_vfprintf_snf.v:55)
     Fp  = sp0 + 0x30            musl vsnprintf's FILE (FMsnprintfI.v:39 FO; FMsnprintfGvf.v:4)
     CK  = Fp + 0xe8 = Fp + 232  its cookie {s, n} (FMsnprintfI.v:40 CKO)
     D   = S + 0x40, dn = 32     the destination: a 32-byte buffer in the snprintf caller's frame, above the
                                 interceptor's va area (sp0 + 0xa08, FMsnprintfGI.v:15) and its five register slots,
                                 so GXA (3) (FMsnprintfSx.v:243) holds through its right disjunct
   The store sat_m is built here, as seam_calls_ready is a statement about a store only: every ASan shadow byte is
   present and 0 (no poison), the runtime cells the three predicates read (FMgxa_mem.v:136-141, :222-228;
   RT_gxa_strnlen.v:100-104) hold their values, and the stack window, the FILE, the cookie and the destination are
   present.  A store that a munch over the footprint reaches keeps the shadow (meta_kept) and every byte below the
   footprint (munch), so it keeps the shadow facts (AsanFacts.shadow_rw_kept) and the cells; each clause then closes
   through the predicates' own introduction lemmas (FMgxa_mem.copy_ready_intro / set_ready_intro,
   RT_gxa_strnlen.strn_ready_intro), whose global shadow_rw this store has.  FMgxaSeamReady.v's local intros
   (copy_ready_intro_loc etc.) are not needed: they replace shadow_rw by per-range hulls, which a store with its whole
   shadow present makes redundant.  Nothing in the witness is abstract. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP09 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v RT_IImgA.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YO0f.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YG0f.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Mem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Frame.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX.G_printf_core_common.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_printf_core_common.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_vfprintf_snf.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.AsanFacts.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.CopyCall.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.SetCall.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.StrnlenCall.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.ImageA.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Cells.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Step.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.Shadow.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.R_m2s.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_memcpyw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_memsetw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_memchrw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_strnlenw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FMupoison.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_gxa_calls_mem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_gxa_calls.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FMgxaSeamGuard.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FMgxaSeamReady.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Module YO := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YO0f.
Module YG := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YG0f.
Module CJM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Mem.
Module CJF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Frame.
Module GXI := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
Module GCA := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_printf_core_common.G_printf_iface.
Module GV := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_vfprintf_snf.
Module GAF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.AsanFacts.
Module GCC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.CopyCall.
Module GSC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.SetCall.
Module GNC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.StrnlenCall.
Module BzI := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.ImageA.
Module BzCl := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Cells.
Module BzSt := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Step.
Module BSh := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.Shadow.
Module BR := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.R_m2s.
Module BMW := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_memcpyw.
Module BSW := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_memsetw.
Module BCW := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_memchrw.
Module BNW := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.I_strnlenw.
Module FU := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FMupoison.
Module FMM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_gxa_calls_mem.
Module RSN := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_gxa_calls.
Module SG := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FMgxaSeamGuard.
Module NR := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FMgxaSeamReady.

#[local] Existing Instance A_img.

(* ===================================================================================== *)
(* 1. the geometry                                                                        *)
(* ===================================================================================== *)

Definition SAT_S : Z := 0x7fffffffe000.          (* the snprintf caller's sp *)
Definition SAT_q : Z := SAT_S - 0xa30.           (* sp0, musl vfprintf's entry sp *)
Definition SAT_lo : Z := SAT_q - 5552.           (* sp0 - VFA_DEPTH *)
Definition SAT_Fp : Z := SAT_q + 0x30.           (* sp0 + FO, musl vsnprintf's FILE *)
Definition SAT_CK : Z := SAT_Fp + 0xe8.          (* sp0 + CKO, its cookie *)
Definition SAT_D : Z := SAT_S + 0x40.            (* the destination, in the snprintf caller's frame *)
Definition SAT_dn : nat := 32.

(* the runtime cells all lie below this bound, far below the footprint *)
Definition CELL_TOP : Z := 0x140000.

Lemma sat_eqs :
  SAT_q = 0x7fffffffd5d0 /\ SAT_lo = 0x7fffffffc020 /\ SAT_Fp = 0x7fffffffd600 /\ SAT_CK = 0x7fffffffd6e8 /\
  SAT_D = 0x7fffffffe040 /\ Z.of_nat SAT_dn = 32 /\ CELL_TOP = 0x140000 /\
  GCA.OUT_DEPTH = 4640 /\ GSC.SET_DEPTH = 2224 /\ GNC.STRN_DEPTH = 4384 /\ GCC.COPY_DEPTH = 2240 /\
  GXI.SNF_CAP = 80 /\ GV.VFA_DEPTH = 5552 /\ BR.kHighShadowEnd = 0x10007fff7fff /\
  GAF.HIGHMEM_BEG = 0x10007fff8000 /\ GAF.APPMEM_END = 0x800000000000 /\ YG.kHighMemBeg = 0x10007fff8000.
Proof. repeat split. all: reflexivity. Qed.

Local Ltac geo := generalize sat_eqs; lia.

(* ===================================================================================== *)
(* 2. the store                                                                           *)
(* ===================================================================================== *)

(* ASan's shadow, as AsanFacts.in_shadow (AsanFacts.v:17) *)
Definition sat_shadow_b (a : Z) : bool :=
  (GAF.LOWMEM_END <=? a) && (a <? GAF.LOWSHADOW_END) || (GAF.HIGHSHADOW_BEG <=? a) && (a <? GAF.HIGHMEM_BEG).

(* the runtime cells (address, width, value), each the cell of one of the six cell predicates:
   R_m2s.m2s_cells, I_memcpyw.icells, I_memsetw.icells_ms, I_strnlenw.icells_sn / icells_sns, I_memchrw.icells_mc *)
Definition sat_cells : list (Z * nat * Z) :=
  [(0x9d9c0, 8%nat, 0x137be8);        (* GOT: common_flags_dont_use *)
   (0x9d9d0, 8%nat, 0xa60b8);         (* GOT: __asan_shadow_memory_dynamic_address *)
   (0x9d9d8, 8%nat, 0xa6da8);         (* GOT: kMidMemBeg *)
   (0x9d9e0, 8%nat, 0xa6db0);         (* GOT: kMidMemEnd *)
   (0x9d9e8, 8%nat, 0xa6da0);         (* GOT: kHighMemEnd *)
   (0x9e538, 8%nat, 0xa6d99);         (* GOT: the flag byte *)
   (0x9f728, 8%nat, 0x963d0);         (* REAL(memchr) = musl memchr *)
   (0x9f818, 8%nat, 0x96e48);         (* REAL(strnlen) = musl strnlen *)
   (0x9f868, 8%nat, 0x964cc);         (* REAL(memcpy) = musl memcpy *)
   (0x9f870, 8%nat, 0x96900);         (* REAL(memset) = musl memset *)
   (0xa60b8, 8%nat, 0x7fff8000);      (* the shadow offset *)
   (0xa6d98, 1%nat, 1);               (* asan_inited *)
   (0xa6d99, 1%nat, 1);               (* the flag byte *)
   (0xa6da0, 8%nat, 0x7fffffffffff);  (* kHighMemEnd *)
   (0xa6da8, 8%nat, 0);               (* kMidMemBeg *)
   (0xa6db0, 8%nat, 0);               (* kMidMemEnd *)
   (0x137ce3, 1%nat, 1)].             (* common_flags_dont_use + 251 *)

Fixpoint cell_byte (cs : list (Z * nat * Z)) (a : Z) : option Z :=
  match cs with
  | [] => None
  | (b, w, v) :: cs' =>
      if (b <=? a) && (a <? b + Z.of_nat w) then Some (YO.le_byte v w (Z.to_nat (a - b))) else cell_byte cs' a
  end.

(* the application bytes the clauses name: the stack window, the FILE and the cookie (one interval, [lo, CK + 16)),
   and the destination *)
Definition sat_app_b (a : Z) : bool :=
  (SAT_lo <=? a) && (a <? SAT_CK + 16) || (SAT_D <=? a) && (a <? SAT_D + Z.of_nat SAT_dn).

Definition sat_byte (a : Z) : option byte :=
  if sat_shadow_b a then Some (Z_to_bv 8 0)
  else match cell_byte sat_cells a with
       | Some z => Some (Z_to_bv 8 z)
       | None => if sat_app_b a then Some (Z_to_bv 8 0) else None
       end.

Definition sat_m (x : word) : option byte := sat_byte (bv_unsigned x).

(* ---- the shadow: present and 0 ---- *)
Lemma sat_m_shadow : forall s, GAF.in_shadow s -> sat_m (CJM.wa s) = Some (Z_to_bv 8 0).
Proof.
intros s Hs. pose proof (GAF.in_shadow_range s Hs) as [R0 R1].
unfold sat_m. rewrite CJM.wa_unsigned by lia. unfold sat_byte.
replace (sat_shadow_b s) with true; [reflexivity|].
symmetry. unfold sat_shadow_b. unfold GAF.in_shadow in Hs.
destruct Hs as [Hs|Hs]; apply orb_true_iff; [left|right]; apply andb_true_iff;
  (split; [apply Z.leb_le | apply Z.ltb_lt]); lia.
Qed.

Lemma sat_shadow_rw : GAF.shadow_rw sat_m.
Proof.
intros a Ha. unfold wview, CJM.mrd. rewrite (sat_m_shadow a Ha).
split; [discriminate | eexists; reflexivity].
Qed.

Lemma sat_addr_byte : forall a, GAF.app_mem a -> GAF.addr_byte sat_m a.
Proof.
intros a Ha. split; [exact Ha|]. exists (Z_to_bv 8 0). split.
- unfold CJM.mrd. rewrite (sat_m_shadow _ (GAF.shadow_of_app a Ha)). reflexivity.
- unfold GAF.shadow_ok. left. reflexivity.
Qed.

(* every high range that ends 7 bytes below 2^47 is addressable for GXA *)
Lemma sat_pf_rng : forall p n,
  GAF.HIGHMEM_BEG <= p -> 0 <= n <= 2 ^ 40 -> p + n + 7 <= GAF.APPMEM_END -> GAF.pf_rng sat_m p n.
Proof.
intros p n H1 H2 H3.
split; [lia|]. split; [|split].
- split; [unfold GAF.HIGHMEM_BEG in H1; lia|]. split; [lia|]. split; [lia|].
  intros i Hi. apply sat_addr_byte. unfold GAF.app_mem. lia.
- unfold GAF.end_in_app. right. unfold GAF.app_mem. lia.
- intros i Hi. unfold GAF.app_mem. lia.
Qed.

(* ---- the runtime cells, at every store that agrees with sat_m below CELL_TOP ---- *)
Definition cell_ok_b (a : Z) (w : nat) (v : Z) : bool :=
  forallb (fun k => negb (sat_shadow_b (a + Z.of_nat k)) &&
                    match cell_byte sat_cells (a + Z.of_nat k) with
                    | Some z => Z.eqb z (YO.le_byte v w k)
                    | None => false
                    end) (seq 0 w).

Lemma sat_val_mem : forall (m' : word -> option byte) a w v,
  (forall x : word, bv_unsigned x < CELL_TOP -> m' x = sat_m x) ->
  0 <= a -> a + Z.of_nat w <= CELL_TOP -> cell_ok_b a w v = true ->
  val_mem tfibsegs m' a w v.
Proof.
intros m' a w v AG Ha Haw OK k Hk.
unfold cell_ok_b in OK. rewrite forallb_forall in OK.
specialize (OK k ltac:(apply in_seq; lia)). cbv beta in OK.
apply andb_true_iff in OK as [E1 E2]. apply negb_true_iff in E1.
destruct (cell_byte sat_cells (a + Z.of_nat k)) as [z|] eqn:E3; [|discriminate E2].
apply Z.eqb_eq in E2.
unfold CELL_TOP in AG, Haw. unfold mbyte.
rewrite AG by (rewrite FU.wz by lia; lia).
unfold sat_m. rewrite FU.wz by lia. unfold sat_byte. rewrite E1, E3, E2. reflexivity.
Qed.

Local Ltac c8 AG := eapply NR.c8_of_val_mem;
  [lia | lia | lia | apply (sat_val_mem _ _ _ _ AG); [lia | unfold CELL_TOP; lia | vm_compute; reflexivity]].
Local Ltac c1 AG := eapply NR.c1_of_val_mem;
  [lia | lia | lia | apply (sat_val_mem _ _ _ _ AG); [lia | unfold CELL_TOP; lia | vm_compute; reflexivity]].

(* the six cell predicates the three ready predicates carry (as FMgxaSeamReady.cells_of_agree, from sat_m) *)
Lemma sat_cells_at : forall m' : word -> option byte,
  (forall x : word, bv_unsigned x < CELL_TOP -> m' x = sat_m x) ->
  BR.m2s_cells m' /\ BMW.icells m' /\ BSW.icells_ms m' /\ BNW.icells_sn m' /\ BCW.icells_mc m' /\ BNW.icells_sns m'.
Proof.
intros m' AG.
split; [|split; [|split; [|split; [|split]]]].
- unfold BR.m2s_cells, BSh.SHB, BR.kHighMemEnd.
  split; [|split]; (apply NR.rw_of_ro; [|vm_compute; reflexivity]).
  + apply NR.cells_cons8; [c8 AG|]. apply NR.cells_cons8; [c8 AG|]. apply NR.cells_cons8; [c8 AG|]. c8 AG.
  + c8 AG.
  + apply NR.cells_cons8; [c8 AG|]. apply NR.cells_cons8; [c8 AG|]. c8 AG.
- unfold BMW.icells. split; [c8 AG|]. split; [c8 AG|]. split; [c8 AG|]. split; [c8 AG | c1 AG].
- unfold BSW.icells_ms. split; [c8 AG|]. split; [c8 AG|]. split; [c8 AG|]. split; [c8 AG | c1 AG].
- unfold BNW.icells_sn. split; [c8 AG|]. split; [c8 AG|]. split; [c8 AG|].
  split; [apply NR.rw_of_ro; [c1 AG | vm_compute; reflexivity] | c1 AG].
- unfold BCW.icells_mc. split; [c8 AG|]. split; [c8 AG|].
  split; [c8 AG | apply NR.rw_of_ro; [c1 AG | vm_compute; reflexivity]].
- unfold BNW.icells_sns. c8 AG.
Qed.

(* a munch over the seam's footprint keeps every byte below CELL_TOP *)
Lemma sat_agree : forall m' : word -> option byte,
  CJF.munch (GV.vf_snf_fp SAT_lo SAT_q SAT_Fp SAT_CK SAT_D SAT_dn) sat_m m' ->
  forall x : word, bv_unsigned x < CELL_TOP -> m' x = sat_m x.
Proof.
intros m' MU x Hx. apply MU. unfold GV.vf_snf_fp. cbn [CJF.outside].
split; [geo|]. split; [geo|]. split; [geo|]. split; [geo | exact I].
Qed.

(* ===================================================================================== *)
(* 3. READY's clauses at the witness                                                      *)
(* ===================================================================================== *)

Theorem seam_ready_fm :
  SG.seam_calls_ready FMM.copy_ready FMM.set_ready RSN.strn_ready sat_m SAT_q SAT_lo SAT_Fp SAT_CK SAT_D SAT_dn.
Proof.
unfold SG.seam_calls_ready. intros m' MU WM MK.
pose proof (sat_cells_at m' (sat_agree m' MU)) as (C1 & C2 & C3 & C4 & C5 & C6).
pose proof (GAF.shadow_rw_kept sat_m m' sat_shadow_rw MK WM) as SRW.
split; [|split].
- (* memcpy, with the sink's frame at sp - 64 *)
  intros sp Dst P N H1 H2 HDst HN HP.
  assert (PD : GAF.pf_rng m' Dst N).
  { apply (GAF.pf_rng_kept sat_m m' Dst N); [|exact MK].
    destruct HDst as [[HD1 HD2]|[HD1 HD2]]; apply sat_pf_rng; geo. }
  assert (PS : GAF.pf_rng m' P N).
  { destruct HP as [[-> HP]|[[HP1 HP2]|HP]].
    - apply (GAF.pf_rng_kept sat_m m' _ N); [apply sat_pf_rng; geo | exact MK].
    - apply (GAF.pf_rng_kept sat_m m' P N); [apply sat_pf_rng; geo | exact MK].
    - exact (GAF.pf_rng_kept sat_m m' P N HP MK). }
  apply (FMM.copy_ready_intro m' (sp - 64) Dst P N N N); [geo | geo | exact HN | | exact PD | exact PS | exact SRW
                                                         | lia | lia | exact C1 | exact C2].
  right; right. destruct HDst as [[HD1 HD2]|[HD1 HD2]]; geo.
- (* memset *)
  intros sp Dst N H1 H2 H3.
  destruct (Z_le_gt_dec 0 N) as [HN|HN]; [|intros HN'; lia].
  apply (FMM.set_ready_intro m' sp Dst N N); [geo | geo | exact HN | right; right; exact H2 | | exact SRW | lia
                                             | exact C1 | exact C3].
  apply (GAF.pf_rng_kept sat_m m' Dst N); [apply sat_pf_rng; geo | exact MK].
- (* strnlen *)
  intros sp S0 N L buf H1 H2 PR HL.
  apply (RSN.strn_ready_intro m' sp S0 N L buf); [geo | geo | exact (GAF.pf_rng_kept sat_m m' S0 L PR MK)
                                                 | exact SRW | exact HL | exact C1 | exact C4 | exact C5 | exact C6].
Qed.

(* each clause bites: the three predicates hold at sat_m at one call each clause covers, with a non-empty range *)
Corollary seam_ready_sat_calls :
  FMM.copy_ready sat_m (SAT_q - 368 - 64) SAT_D (SAT_q - 352) 32 /\
  FMM.set_ready sat_m (SAT_lo + GSC.SET_DEPTH) (SAT_lo + GSC.SET_DEPTH) 64 /\
  RSN.strn_ready sat_m (SAT_q - 368) SAT_D 32 [].
Proof.
destruct (seam_ready_fm sat_m (CJF.munch_refl _ _) (fun x H => H) (fun a _ => eq_refl)) as (RC & RS & RT).
split; [|split].
- apply (RC (SAT_q - 368) SAT_D (SAT_q - 352) 32); [geo | geo | left; geo | lia | left; geo].
- apply (RS (SAT_lo + GSC.SET_DEPTH) (SAT_lo + GSC.SET_DEPTH) 64); geo.
- apply (RT (SAT_q - 368) SAT_D 32 32 []); [geo | geo | apply sat_pf_rng; geo | apply Z.leb_le; reflexivity].
Qed.

(* ===================================================================================== *)
(* 4. the satisfiability control                                                          *)
(* ===================================================================================== *)

Theorem seam_ready_sat : exists (m : word -> option byte) (q lo Fp CK D : Z) (dn : nat),
  (YG.kHighMemBeg <= lo /\ q <= 2 ^ 47 /\ q - lo = GV.VFA_DEPTH /\
   lo + GCA.OUT_DEPTH <= q - 368 /\ lo + GSC.SET_DEPTH <= q - 368 /\ lo + GNC.STRN_DEPTH <= q - 368 /\
   q <= Fp /\ Fp + 232 <= CK /\ CK + 16 <= 2 ^ 47 /\
   0 < Z.of_nat dn /\ (D + Z.of_nat dn <= lo \/ q <= D) /\ D + Z.of_nat dn + 8 <= 2 ^ 47 /\
   GAF.pf_rng m lo (q - lo) /\ GAF.pf_rng m D (Z.of_nat dn)) /\
  SG.seam_calls_ready FMM.copy_ready FMM.set_ready RSN.strn_ready m q lo Fp CK D dn.
Proof.
exists sat_m, SAT_q, SAT_lo, SAT_Fp, SAT_CK, SAT_D, SAT_dn.
split; [|exact seam_ready_fm].
do 12 (split; [geo|]).
split; apply sat_pf_rng; geo.
Qed.
