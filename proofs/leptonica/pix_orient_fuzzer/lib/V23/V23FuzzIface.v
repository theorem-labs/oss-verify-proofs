(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim Hoare ShapeAlg AllocIface PureModel VmLedger FPSteps.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Room.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Definition LEPT_STACK : Z := 16384.          (* [comment removed for export] *)
Definition PC_FUZZ : Z := 0x635e0.           (* [comment removed for export] *)
Definition A_LEPT_SEV : Z := 0x127c60.        (* [comment removed for export] *)
Definition A_LEPT_HANDLER : Z := 0x127c68.    (* [comment removed for export] *)
Definition A_LEPT_PMM : Z := 0x127c78.        (* [comment removed for export] *)
Definition A_MORPH_BC : Z := 0x127ca0.        (* [comment removed for export] *)
Definition A_EMPTY : Z := 0x137f20.           (* [comment removed for export] *)
Definition A_GOT_LO : Z := 0x126a10.          (* [comment removed for export] *)
Definition A_GOT_HI : Z := 0x126c38.

(* [comment removed for export] *)
Definition FUZZ_CALLS : Z := 1024.
Definition fuzz_margin (size : Z) : Z := 2^31 - 2^26.      (* [comment removed for export] *)
Definition FUZZ_BMAX : Z := 2^31 - 2^26.

Lemma fuzz_calls_nonneg : 0 <= FUZZ_CALLS.
Proof. unfold FUZZ_CALLS. lia. Qed.
Lemma fuzz_margin_bound : forall size, 0 <= size < 2^26 -> 0 <= fuzz_margin size <= FUZZ_BMAX.
Proof. intros size H. unfold fuzz_margin, FUZZ_BMAX. lia. Qed.
(* [comment removed for export] *)
Lemma fuzz_room_fits : room_k0 FUZZ_CALLS <= ROOM_KMAX /\ room_b0 FUZZ_BMAX <= ROOM_BCAP.
Proof. unfold room_k0, room_b0, DRV_CALLS, DRV_BYTES, FUZZ_CALLS, FUZZ_BMAX, ROOM_KMAX, ROOM_BCAP. lia. Qed.

Section WithLayout.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.

Definition fuzz_call_contract : Prop :=
  forall (fx : FPState) (A : AS) (m : word -> option byte) (md : Model) (regs : bvmap 5 word)
         (dptr : word) (size : Z) (payload : list byte) (ret sp0 : word) (argv envp : list (list byte)) (S : TSet),
    (* [comment removed for export] *)
    frm_zero (@fp_csr fx) ->
    ainv A m (m_vmmaps md) -> md_pure md -> al_env sp0 argv envp m ->
    (* [comment removed for export] *)
    getr regs 10 = dptr -> getr regs 11 = Z_to_bv 64 size -> size = Z.of_nat (length payload) -> size < 2 ^ 26 ->
    (0 < size -> live A dptr = Some size) ->
    (forall i, 0 <= i < size -> m (Z_to_bv 64 (bv_unsigned dptr + i)) = Some (nth (Z.to_nat i) payload (Z_to_bv 8 0))) ->
    (size = 0 -> dptr = Z_to_bv 64 A_EMPTY /\ forall a : word, A_EMPTY <= bv_unsigned a < A_EMPTY + 16 -> m a = None) ->
    bv_unsigned dptr mod 16 = 0 ->
    (* [comment removed for export] *)
    getr regs 1 = ret -> ret_ok ret -> getr regs 3 = Z_to_bv 64 0x10800 -> getr regs 4 = al_gp ->
    bv_unsigned (getr regs 2) mod 16 = 0 ->
    alloc_top (m_vmmaps md) + 8192 + LEPT_STACK <= bv_unsigned (getr regs 2) ->
    bv_unsigned (getr regs 2) <= bv_unsigned sp0 -> bv_unsigned sp0 <= sp_window_hi ->
    init_sp_win (m_vmmaps md) ->
    (forall a : word, bv_unsigned (getr regs 2) - LEPT_STACK <= bv_unsigned a < bv_unsigned (getr regs 2) ->
                      m a <> None /\ ~ owned A a /\ ~ al_in_ro a /\ ~ al_in_rw a) ->
    (* [comment removed for export] *)
    (forall a : word, A_LEPT_SEV <= bv_unsigned a < A_LEPT_SEV + 8 -> m a = None) ->
    (forall a : word, A_LEPT_PMM <= bv_unsigned a < A_LEPT_PMM + 16 -> m a = None) ->
    (forall a : word, A_MORPH_BC <= bv_unsigned a < A_MORPH_BC + 4 -> m a = None) ->
    store_ok al_segs m (Z_to_bv 64 A_LEPT_HANDLER) 8 = true ->
    (forall a : word, A_GOT_LO <= bv_unsigned a < A_GOT_HI -> m a = None) ->
    (* [comment removed for export] *)
    forall (k b : Z), aroom A (m_vmmaps md) k b -> FUZZ_CALLS <= k -> fuzz_margin size <= b ->
    (* [comment removed for export] *)
    (forall (fx' : FPState) A' m' vm' regs',
        frm_zero (@fp_csr fx') ->
        ainv A' m' vm' ->
        (forall q, live A' q = live A q) ->
        getr regs' 10 = Z_to_bv 64 0 ->
        (forall r, callee_saved r -> getr regs' r = getr regs r) ->
        (* [comment removed for export] *)
        (forall a : word, ~ (al_grantable a /\ bv_unsigned a < alloc_top (m_vmmaps md)) -> ~ al_globals a ->
                          ~ al_errno_slot a ->
                          ~ (A_LEPT_HANDLER <= bv_unsigned a < A_LEPT_HANDLER + 8) ->
                          ~ (bv_unsigned (getr regs 2) - LEPT_STACK <= bv_unsigned a < bv_unsigned (getr regs 2)) ->
                          m' a = m a) ->
        (forall q k i, live A q = Some k -> 0 <= i < k -> m' (at_ q i) = m (at_ q i)) ->
        (forall a : word, m a <> None ->
                          bv_unsigned a < al_image_hi \/ (al_grantable a /\ bv_unsigned a < alloc_top (m_vmmaps md))
                          \/ m' a <> None) ->
        vm_limit vm' = vm_limit (m_vmmaps md) -> alloc_top vm' = alloc_top (m_vmmaps md) ->
        vm_init_sp vm' = vm_init_sp (m_vmmaps md) -> vm_reserved vm' = vm_reserved (m_vmmaps md) ->
        aroom A' vm' (k - FUZZ_CALLS) (b - fuzz_margin size) ->
        realizes al_segs (mkCfg (@mkst fx' regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
    realizes al_segs (mkCfg (@mkst fx regs (Z_to_bv 64 PC_FUZZ) m al_rom) md) S.
End WithLayout.
