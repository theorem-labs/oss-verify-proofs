From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import send_line_c relay_event_c RelayFrame RelayRunT RelayRunF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import relay_add_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep ListRep CheckRep ListTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import HarnessTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import TrModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import source_reset_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Definition OP_ADD : Z := 0x141f0.
Definition OP_ADD_FRAME : Z := 32.
Definition OP_ADD_K : Z := OP_ADD_FRAME + Z.max SOURCE_RESET_K (Z.max ALLOC_STACK RELAY_ADD_K).
Definition G_NFD : Z := 0x30fe0.
Definition FIRST_FD : Z := 100.
Definition PARTIAL_BYTES : Z := 6000.

Definition new_src (fd q : Z) (pj : list byte) : hsrc :=
  HS fd 1 0 0 empty_list 0 q pj 0 0 [] empty_list empty_list.

Section OA.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Variable F : ResFormT.
Let segs := ms_segs Bm.
Let MR := aa_MR API.

Definition op_add_contract : Prop :=
  forall L A regs mem md (bnd : rt_R F) (os : list Z) (n0 N C G : Z) (ents tail : list byte),
    let FD := FIRST_FD + n0 in
    ms_segs Bm = rsegs ->
    call_pre_k Bm MR OP_ADD_K L A regs mem md ->
    st_init_done A = true ->
    ro_agree segs mem ->
    (forall a, errno_addr Bm <= a < errno_addr Bm + 4 -> in_img Bm a) ->
    (forall a, G_RELAY_LO <= a < G_S + SRC_SIZE * SOURCES_MAX -> img_plain Bm a) ->
    (forall a, G_WAKE1 <= a < G_WAKE1 + 4 -> img_plain Bm a) ->
    length os = 4%nat ->
    (forall i, (i < 4)%nat ->
       - 2 ^ 31 <= nth i os 0 < 2 ^ 31 /\
       rw_cells segs mem (G_S + SRC_SIZE * Z.of_nat i + 4) [C4 (Z_to_bv 64 (nth i os 0))]) ->
    (forall i, (i < 4)%nat -> nth i os 0 = 0 -> rw_cells segs mem (G_S + SRC_SIZE * Z.of_nat i) [CB 96%nat (nulbytes 96)]) ->
    rw_cells segs mem G_NFD [C4 (Z_to_bv 64 n0)] -> 0 <= n0 <= 512 ->
    rw_cells segs mem G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
    bytes_at segs mem G_WAKE1 (le4 (Z_to_bv 64 (-1))) ->
    rw_cells segs mem G_NSRC [C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 C)] ->
    rw_cells segs mem G_SRC [C8 (Z_to_bv 64 G)] ->
    ((C = 0 /\ G = 0 /\ N = 0 /\ ents = []) \/
     (C = 16 /\ In (G, SRC_TABLE) (blocks L A) /\ fresh_block Bm G SRC_TABLE /\
      Z.of_nat (length ents) = SRC_ENTRY * N /\ Z.of_nat (length tail) = SRC_TABLE - SRC_ENTRY * N /\
      rw_cells segs mem G [CB (Z.to_nat SRC_TABLE) (ents ++ tail)])) ->
    rt_ok F A bnd ->
    (first_zero os <> None -> 0 <= N < 4) ->
    (forall qs, length qs = nretF (op_add_tr (first_zero os) FD N C (known_at L A G)) -> roomF F qs bnd (op_add_tr (first_zero os) FD N C (known_at L A G))) ->
    SR segs (mkCfg (YK11.mkst regs (Z_to_bv 64 OP_ADD) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md',
         c' = mkCfg (YK11.mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         st_init_done A' = true /\
         ro_agree segs mem' /\
         (first_zero os = None ->
            relay_post Bm API OP_ADD_K (fun _ => False) (fun _ => False) L A regs mem md L' A' regs' mem' md' /\
            blocks L' A' = blocks L A /\ rt_ok F A' bnd) /\
         (forall i, first_zero os = Some i ->
            let HA := G_S + SRC_SIZE * Z.of_nat i in
            exists (q G' : Z) (pj rest : list byte),
            relay_post Bm API OP_ADD_K
              (fun a => HA <= a < HA + SRC_SIZE \/ G_NFD <= a < G_NFD + 4 \/
                        G_LOCK + 4 <= a < G_LOCK + 8 \/ G_NSRC <= a < G_NSRC + 8 \/ G_SRC <= a < G_SRC + 8 \/
                        (0 < C /\ G + SRC_ENTRY * N <= a < G + SRC_ENTRY * (N + 1)))
              (fun _ => False)
              L A regs mem md L' A' regs' mem' md' /\
            (exists qs, length qs = nretF (op_add_tr (Some i) FD N C (known_at L A G)) /\ rt_ok F A' (runF F qs bnd (op_add_tr (Some i) FD N C (known_at L A G))) /\
               live_at L' A' (resolveF qs (Ret 0)) q PARTIAL_BYTES /\
               live_at L' A' (resolveF qs (relay_add_tbl FD N C 1 (known_at L A G))) G' SRC_TABLE) /\
            rw_cells segs mem' HA [C4 (Z_to_bv 64 FD); C4 (Z_to_bv 64 1); CB 32%nat (nulbytes 32);
                                   C8 (Z_to_bv 64 q); CB 48%nat (nulbytes 48)] /\
            src_at Bm L' A' mem' HA (new_src FD q pj) /\
            rw_cells segs mem' G_NFD [C4 (Z_to_bv 64 (n0 + 1))] /\
            rw_cells segs mem' G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] /\
            bytes_at segs mem' G_WAKE1 (le4 (Z_to_bv 64 (-1))) /\
            rw_cells segs mem' G_NSRC [C4 (Z_to_bv 64 (N + 1)); C4 (Z_to_bv 64 16)] /\
            rw_cells segs mem' G_SRC [C8 (Z_to_bv 64 G')] /\
            In (G', SRC_TABLE) (blocks L' A') /\ fresh_block Bm G' SRC_TABLE /\
            Z.of_nat (length rest) = SRC_TABLE - SRC_ENTRY * (N + 1) /\
            rw_cells segs mem' G' [CB (Z.to_nat SRC_TABLE) (ents ++ new_entry FD ++ rest)] /\
            In (q, PARTIAL_BYTES) (blocks L' A') /\ fresh_block Bm q PARTIAL_BYTES /\
            (forall p m, In (p, m) (blocks L A) -> 0 < m -> p <> q) /\
            ((C = 0 /\ (forall p m, In (p, m) (blocks L A) -> 0 < m -> p <> G') /\
              exists c1 c2 d1 d2, blocks L' A' = c1 ++ (G', SRC_TABLE) :: c2 /\ c1 ++ c2 = d1 ++ (q, PARTIAL_BYTES) :: d2 /\
                d1 ++ d2 = blocks L A) \/
             (C = 16 /\ G' = G /\ rest = skipn (Z.to_nat SRC_ENTRY) tail /\
              exists d1 d2, blocks L' A' = d1 ++ (q, PARTIAL_BYTES) :: d2 /\ d1 ++ d2 = blocks L A)))).

End OA.
