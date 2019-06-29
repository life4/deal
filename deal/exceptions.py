

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


class OfflineContractError(ContractError):
    pass


class SilentContractError(ContractError):
    pass
