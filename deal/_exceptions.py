

class ContractError(AssertionError):
    pass


class PreContractError(ContractError):
    pass


class PostContractError(ContractError):
    pass


class InvContractError(ContractError):
    pass


class RaisesContractError(ContractError):
    pass


class ReasonContractError(ContractError):
    pass


class MarkerError(ContractError):
    pass


class OfflineContractError(MarkerError):
    pass


class SilentContractError(MarkerError):
    pass
