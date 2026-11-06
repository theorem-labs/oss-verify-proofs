From OSSVerify.libreac.fuzz_pcap Require Symbols.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Contract.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import Mem Cells Step.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Frame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel fclose_c pcap_source_struct.
Import ListNotations.
Local Open Scope Z_scope.

Definition PCAP_SOURCE_CLOSE : Z := Eval compute in Symbols.Ubsan.s_pcap_source_close.
Definition CLOSE_K : Z := 8256.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition close_writes (ps h : Z) (a : Z) : Prop :=
  h <> 0 /\ (fclose_writes h a \/ ps <= a < ps + 8).

Definition pcap_source_close_contract : Prop :=
  forall L A regs mem md (ps h : Z) (sw olen vtag vid : word) (pad : list byte) (b p : Z) (Fc : list byte)
         (b0 : sbound),
    segs = rsegs ->
    call_pre_k B MR CLOSE_K L A regs mem md ->
    getr regs 10 = Z_to_bv 64 ps -> ps <> 0 -> ps mod 8 = 0 -> spZ regs <= ps ->
    rw_cells rsegs mem ps (ps_cells (wz h) sw olen vtag vid pad) -> 0 <= h < 2 ^ 64 ->
    (h <> 0 ->
       In (h, 1304) (blocks L A) /\ In (b, Z.of_nat (length Fc)) (blocks L A) /\
       mstl mem h b Fc p (wz 0) (wz 0) /\ ofl_one mem h /\ stdio_ok mem) ->
    guard_ok mem -> ro_agree segs mem -> res_ok_slots A b0 ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 PCAP_SOURCE_CLOSE) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md',
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         call_post_k B MR CLOSE_K L A regs mem md (close_writes ps h) L' A' regs' mem' md' /\
         rw_cells rsegs mem' ps (ps_cells (wz 0) sw olen vtag vid pad) /\
         guard_ok mem' /\ ro_agree segs mem' /\
         (h = 0 ->
            L' = L /\ A' = A /\ md' = md /\ Frame.munch [(spZ regs - 16, spZ regs)] mem mem' /\
            res_ok_slots A' b0) /\
         (h <> 0 ->
            (exists b1 b2, blocks L A = b1 ++ (h, 1304) :: b2 /\ blocks L' A' = b1 ++ b2) /\
            blocks_kept B L A mem mem' (fun a => a = h) /\
            (forall q k, In (q, k) (user_blocks A) -> ptr_addr L q <> h -> In (q, k) (user_blocks A')) /\
            (st_init_done A = true -> st_init_done A' = true) /\
            (length (st_regions A) <= length (st_regions A'))%nat /\
            res_ok_slots A' (sb_free b0 1304) /\
            ofl_empty mem' /\ stdio_ok mem' /\ bytes_at rsegs mem' b Fc)).

End K.
